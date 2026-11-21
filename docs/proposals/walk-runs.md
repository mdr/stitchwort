# A walk for the read-back: `Parse.Runs` as a walk family

**Status:** design note, 21 November 2026 (SW-4522, an Opus paper lane,
from [SW-4519's map](../reviews/SW-4519-slice1-shortening-map.md) lane 3).
Nothing is built. The decision in [§6](#6-the-decision-for-matt) is
Matt's. Read against `main` at `452034106`.

How claims are marked:

- **[measured]**: counted today with SW-4519's `count.py` and two small
  scans of its output (classification by the conclusion after the last
  `):`, as in the map; a proof line is "plumbing" when it is a lone
  argument, a thunk `(() => …)`, a short continuation `(x => …)`, a
  `runsBind`/`runsLook`/`runsMap`/`runsSame`/`runsPure` head, or a
  `byComputing`/`appendNil` join; scripts in [`walk-runs/`](walk-runs/),
  run on `count.py`'s output);
- **[read]**: read in the file named;
- **[estimated]**: my judgement, mostly from the ten-theorem sample in §1.

## In plain words

**The problem.** 205 slice 1 theorems (4,933 proof lines) prove that a
parser *does* read what it should: `Parse.Runs p read rest value`. None
use the walk. Their proofs spell out every step of the parser by hand,
passing each step the parser, its continuation, the part it reads, the
part after it and the value, one per line: about 71% of the `Runs` proof
lines are that bookkeeping [measured]. The walk can't take them because
`Runs` describes a run by *how the input splits* (`read` and `rest`), and
working out a split is subtraction on lists, which unification can't do.

**The change.** Describe a run by *where it stops* instead: a new
`Parse.RunsOn p input rest value` ("`p`, run on `input`, stops with `rest`
left and gives `value`"), with `Parse.Runs p read rest value` redefined as
`RunsOn p (read ++ rest) rest value` (the same proposition). Then a
sequence is a chain, `input → mid → rest`, that unification follows step
by step with no subtraction. Teach the walk two things it lacks for this:
a family whose bind lemma fixes the value instead of quantifying over it,
and a split that a hypothesis already decides (`numeral:
negativeNumeral … = True`) is taken, not split.

**What it should do.** About 2,000 to 2,450 of the 3,242 proof lines in
the 179 parser-run theorems go [estimated]; a 31-line proof like
`runsNegativeNumber` becomes `byWalking []`. 26 theorems (1,691 lines)
that conclude read-back *records* (`AtomReads`, `MulReads`, …) are not
parser runs and gain nothing here. No new syntax, no new attribute, no
statement changes meaning, nothing in the kernel.

## 1. What these proofs look like

### 1.1 The set

| Conclusion | Theorems | Proof lines | Plumbing [measured] | Main file |
|---|---|---|---|---|
| `Parse.Runs` | 121 | 2,465 | 71% | `Syntax/ReadBackRuns.sw` (1,751 of the 4,933) |
| `Parse.RunsFrom` (one state) | 16 | 449 | 56% | `Syntax/LexProofs.sw`, `ReadBackProofs.sw` |
| `ItemReads` (a `RunsFrom` of the lexer's `item`) | 42 | 328 | 33% | `Syntax/LexProofs.sw` |
| read-back records (`AtomReads`, `MulReads`, `AppReads`, …) | 26 | 1,691 | 33% | `Syntax/ReadBackHung*.sw` |
| **All** | **205** | **4,933** | | |

[measured; the totals match SW-4519's.] In the `Runs` and `RunsFrom`
proofs: 61 `Parse.runsBind`, 102 `runsLook` (the formatter's own bind for a
step that reads nothing), 32 `Parse.runsMap`, 30 `runsSame`, 22
`Parse.runsFromBind`, 75 `Parse.runsPure`; 477 `rewrite`s, 40
`List.appendAssoc`, 36 `List.appendNil`; 21 proofs open the definition
(`state starts honest =>`) [measured].

The records are a different kind of proof. `AtomReads` is `∃ item more =>
read = [item, ..more] ∧ …` [read, `ReadBackTree.sw:165`], and `atomHung`
(419 lines) builds those witnesses and facts from the printer's output
and the hang state: no parser runs in it [read]. They are kind A (`_`,
implicits) and kind D (`byFacts`) of SW-4519's map, not this note's.

### 1.2 The sample

Ten theorems drawn at random (seed 4522, each proof line equally likely)
from the 205, plus SW-4519's `runsUnaryPrefix` and two read for the shape;
four of the draw were records, set aside above. For each, the lines left
under option E (the recommendation, §3.4) and option H (std lemmas only,
§3.1) [estimated; the two marked * I read only in part]:

| Theorem (file) | Lines | E: after | H: after | Why lines stay |
|---|---|---|---|---|
| `runsNegativeNumber` (ReadBackRuns) | 31 | 1 | 5 | |
| `runsUnaryPrefix` (ReadBackRuns) | 39 | 2 | 10 | |
| `runsPipedRange` (ReadBackRuns) | 45 | 3 | 14 | a `||` guard taken apart |
| `runsExprInline` (ReadBackRuns) | 61 | 2 | 12 | |
| `runsAtomAfterPlain` (ReadBackRuns) | 35 | 25 | 25 | uses the state (`mark().left` as fuel): hand, either way |
| `runsTuple` (ReadBackRuns) | 87 | 10 | 35 | `++` re-associated; the loop's hypothesis |
| `runsCommaListFrom` (ReadBackRuns) | 55 | 8 | 20 | the proof's own `match steps` and recursion |
| `runsDeclarationDef`* (ReadBackRuns) | 82 | 15 | 40 | |
| `runsBlockOneLine`* (ReadBackProofs, `RunsFrom`) | 23 | 8 | 15 | stage 5 |
| `itemReadsComment` (LexProofs, `ItemReads`) | 43 | 15 | 25 | stage 5; values carry offsets |
| **All ten** | **501** | **89 (−82%)** | **201 (−60%)** | |

### 1.3 Two of them

`runsNegativeNumber`, today [read, `ReadBackRuns.sw:316`]:

```
theorem runsNegativeNumber ∀ (self: Goal → {Parse Item} Expr) (modes: Modes) (minus number: Item) (rest: List Item)
    (numeral: negativeNumeral [minus, number, ..rest] = True):
    Parse.Runs
      (() => negativeAtom self modes)
      [minus, number]
      rest
      (Prefix minus.leaf.word (Atom number.kind number.leaf.word)) :=
  runsLook
    (() => left())
    (items => negativeAtomOn self modes items)
    [minus, number, ..rest]
    [minus, number]
    rest _
    (runsLeftOn [minus, number, ..rest])
    (rewrite numeral then
      Parse.runsBind
        (() => bump()) _
        [minus]
        [number]
        [minus, number]
        rest
        minus.leaf.word _
        byComputing
        (runsBump minus [number, ..rest])
        (runsLook
          (() => left())
          (items => numberAfter minus.leaf.word items)
          [number, ..rest]
          [number]
          rest _
          (runsLeftOn [number, ..rest])
          (Parse.runsMap
            (() => bump())
            (word => Prefix minus.leaf.word (Atom number.kind word))
            [number]
            rest
            number.leaf.word
            (runsBump number rest))))
```

Everything in it but `rewrite numeral` is fixed by the parser's code: the
steps (`left`, `bump`, `left`, `bump`), the continuations (the code after
each), the reads (one item per `bump`), the values (what `runsLeftOn` and
`runsBump` say). What a reader wants is the statement and:

```
  byWalking []
```

with `runsLeftOn` and `runsBump` registered `@[walk]` in the namespace, and
`numeral` taking the `negativeNumeral` test the code makes.

`runsExprInline` (61 lines, [read, `ReadBackRuns.sw:1977`]) is seven
`runsLook`s, one per look-ahead `exprInline` makes (`modes.peek`,
`walkHere`, `lambdaHere`, …), each passed its lemma and a hypothesis that
says the look-ahead finds nothing (`noWalk`, `noLambda`, …), ending in the
hypothesis `opRuns`. Each look is six lines of values the code fixes and
one line of content. What a reader wants:

```
  byWalking [peekFirst modes item (more ++ rest) open]
```

the hypotheses filling the lemmas' premises, and `notKeyword`,
`notQuantifier`, `notIf` taking the code's tests.

## 2. Why the walk can't take them today

**What the walk needs** [read, `crates/elab/src/walk/registry.rs:73-108`,
`mod.rs` header, `docs/syntax.md` "byWalking"]. A family is a relation
`R … (() => code) post`. Its `@[walk.bind]` lemma is about `() => j (p())`,
with a first explicit premise in a relation about `p` and a **last premise
that is a `∀` over `p`'s results**, `(rest: ∀ v => first v → R … (() => j
v) post)`. The walk solves the first premise with the call's lemma
(read off the callee, "before the goal is looked at"), then goes on into
`j v` with `v` a fresh name and its fact in scope. A last premise that
binds nothing is refused: "`E-WALK-LEMMA`: its last premise binds nothing,
so the walk has no value to hand `j`". Every family today (`Gives`,
`ReadsIn`, `ReadsAt`, `Follows`) is a *post* family: it says what holds of
whatever comes out, so quantifying over the value is natural.

**What `Runs` has** [read, `crates/elab/src/std/Parse/Runs.sw:639`]:

```
theorem Parse.runsBind ∀ (p: () → {Parse t} a) (j: a → {Parse t} b) (first next read rest: List t) (v: a) (value: b)
    (joined: read = first ++ next)
    (runsFirst: Parse.Runs p first (next ++ rest) v)
    (runsNext: Parse.Runs (() => j v) next rest value):
    Parse.Runs (() => j (p())) read rest value
```

Three things stop it fitting, and they are separate:

1. **The value is fixed, not quantified.** `Runs` is completeness: the run
   gives *this* `v`. `runsNext` is about `j v` for the `v` the first step
   gave; there is no `∀`. The registry refuses it (above), and the walk's
   step has nowhere to put a fixed value.
2. **The split is not something unification can find.** The goal fixes
   `read` and `rest`; the callee's lemma fixes `first` (`runsBump` says
   `[item]`; a hypothesis `operandRuns: Runs … read rest operand` says
   `read`). `next` is then "`read` minus `first`": `read =?= first ++ ?next`
   is solved only when `read` is literally a cons list starting with
   `first`. With `read` a variable and `first = read`, `read =?= read ++
   ?next` is stuck (`++` doesn't compute on a variable), which is why the
   hand proofs pass `next` and a `joined` proof (`byComputing`,
   `(List.appendNil read).flipped`) at every step.
3. **Every split but one is dead, and the walk walks them all.** In a
   post family a branch the input can't reach is harmless: `expected`
   "gives anything" (`Parse.givesExpected`). A `Runs` goal on a branch
   that fails is false, so the branch must be ruled out from the
   hypotheses, which is what the hand proofs' `rewrite numeral then`,
   `rewrite notMatch then` and `match peekIn modes 0 rest, noRange with`
   do. The walk splits a stuck scrutinee and walks each branch; it never
   tries to close a branch from its equation and the hypotheses
   [read, `walk/mod.rs` "Steps"; no such step in `walk/`]. Splitting
   would also be wrong in size: a `match` on `sign.kind` has a branch per
   token kind, past the walk's 64-path cap, where the hypothesis `signed`
   or `isComma: comma.kind = Comma` settles it at once.

A fourth, smaller: **statements re-associate `++`.** `runsTuple`'s
hypothesis reads `read1` before `(([comma, ..read2] ++ …) ++ rest)` and the
code reaches it at `(read1 ++ after) ++ rest`; equal lists, not equal
terms. The hand proofs fix these with 40 `List.appendAssoc` rewrites.

`RunsFrom` (and `ItemReads`) add a fifth: the value can depend on the
state (`[located CommentLexeme state.at]`, fuel `mark().left + 1`), so the
run must be followed from one state, and its bind
(`Parse.runsFromBind`) hands `j` a `∀ middle` with the offset reached
[read, `Runs.sw:624`]. That one *is* a `∀`, but over the state, not the
value, and the value is still fixed.

## 3. Options

Figures are for the 179 parser-run theorems (3,242 lines; the records are
out of reach of all of them). Agent-time estimates are already scaled to
past actuals (the median is about 0.33 of a naive estimate).

### 3.1 H: reshape std's lemmas only (no walk)

**What changes.** In std's `Parse/Runs.sw`, add `Parse.RunsOn p input rest
value` (§4.1) and its lemmas with every argument a unification fixes made
implicit (D2422):

```
theorem Parse.runsOnThen ∀ [p: () → {Parse t} a] [j: a → {Parse t} b] [input mid rest: List t] [v: a] [value: b]
    (first: Parse.RunsOn p input mid v)
    (next: Parse.RunsOn (() => j v) mid rest value):
    Parse.RunsOn (() => j (p())) input rest value
```

and `runsOnMap`, `runsOnDone`, `runsOnSame`, the `oneOf`/`many`/`loop`
forms. With `Runs` defined from `RunsOn` (§4.1), every existing `Runs`
hypothesis and lemma fits these as it stands. The hand proofs become
chains like the hand `Gives` chains:

```
  Parse.runsOnThen (runsLeftOn _) (rewrite numeral then
    Parse.runsOnThen (runsBump minus _) (Parse.runsOnThen (runsLeftOn _) (Parse.runsOnMap (runsBump number rest))))
```

`j` is read off the goal as `Parse.readsThen`'s is ("`p` is read off the
first premise, before the goal is looked at, then `j` off the goal",
[read, `Reads.sw:700`]); a lane should confirm on two theorems that the
elaborator does the same for `runsOnThen` before the sweep.

**Cost.** One Sonnet std lane (the relation, ~15 lemmas, the redefinition
and the 104 proofs that open `Runs`'s definition, §4.1): 40 min. The
formatter's migration: two Sonnet or DeepSeek lanes, 35 min each.
**Risk.** Low. Kernel terms are the hand proofs' terms with fewer
arguments to infer; check time should be about today's (unification of
the arguments now written out). Hashes: the std change re-records every
hash snapshot (prelude, examples, projects). **Saves** about 60% of the
3,242 lines: 1,700 to 2,000 [estimated, §1.2].

### 3.2 I: implicit arguments on today's `Parse.runs*` (no new relation)

Make `runsBind`'s arguments implicit as they stand. The split problem
(§2, point 2) remains: wherever `read` isn't a literal list, `next` and
`joined` still have to be written, so most binds keep three or four of
their eleven lines. This is SW-4519's kind A on these files. **Saves**
about 900 to 1,100 lines [estimated: the 1,000-odd lone-argument lines in
these theorems, less the ones unification can't fill]. Cheap (part of
SW-4520's pilot), but a dead end: everything it writes is rewritten
again by H or E.

### 3.3 P: a post family for completeness

**What changes.** A relation in the walk's existing shape, `Parse.Succeeds
p input post` with `post: a → List t → Prop` ("`p` succeeds on `input`,
and `post` holds of its value and what it leaves"), whose bind lemma
quantifies as the others do: `(first: Succeeds p input mid) (rest: ∀ v
left => mid v left → Succeeds (() => j v) left post)`. Callee lemmas give
exact posts (`v = item.leaf.word ∧ left = more`). The walk then needs to
**substitute** those equations at each step, so that `left` becomes
`more` and the next lemma's input fits; today it does that only for the
two-run case (`rewrite <- vFacts` where a fact says `v = vTwin`, [read,
`docs/syntax.md`]). It still needs decided splits and pruning (§2 point
3) and `++` leaves.

**Cost.** Opus walk lane, about 60 min (substitution in one-run families,
decided splits), plus the std lane. **Risk.** Each step adds two `J`
eliminations to the term, and every leaf is a conjunction of equations:
more kernel work than the hand proofs, so more pressure on D3696's 3×
bar for long chains (`runsTuple` has 15 steps). It also keeps two
descriptions of a run (`Runs` and `Succeeds`) that say the same thing
differently. **Saves** about the same as E, 2,000 to 2,400 lines
[estimated]. It is more general: a post can say less than "exactly this
value" (useful for `many` with unknown steps), but nothing in slice 1
needs that.

### 3.4 E: an exact family on `RunsOn` (recommended)

**What changes.**

1. *std* (as H): `Parse.RunsOn`, `Runs` redefined from it, and the three
   family lemmas, tagged: `@[walk.bind] Parse.runsOnThen` (above),
   `@[walk.done] Parse.runsOnDone ∀ [x input rest value] (stays: input =
   rest) (gives: x = value): RunsOn (() => x) input rest value`, and
   `@[walk.weaken] Parse.runsOnWeaken` (another `rest` and value, two
   equation leaves). The primitives get `@[walk]` (`runsOnNext`,
   `runsOnPeek`, `runsOnSpan`, …) and so do the formatter's step lemmas
   in its namespaces (`runsLeftOn`, `runsBump`, `runsPeekOn`,
   `runsWalkHere`, …).
2. *the walk* (`crates/elab/src/walk/`):
   - **Exact families.** The registry accepts a `@[walk.bind]` lemma whose
     last premise is `R … (() => j v) …` with no `∀`, when every variable
     it shares with the first premise (`v`, `mid`) is one of that
     premise's arguments: the callee's lemma fixes them. The step solves
     the first premise as now, then goes on in `j v` with `v` the term
     the callee gave (`minus.leaf.word`, `peekIn modes 0 rest`), not a
     fresh name. A callee that leaves `v` or `mid` unknown is `E-WALK`
     ("the lemma for `f` doesn't say what it gives or where it stops").
     The done and weaken lemmas are ordinary: their premises are leaves.
   - **Decided splits.** Before splitting a stuck scrutinee `c`, the walk
     looks for a hypothesis `c = e` (or `e = c`) with `e` a constructor
     form (`True`, `False`, `Comma`, `Some k`) and rewrites with it, as
     the hand proofs' `rewrite numeral then` does: one path, not one per
     constructor. Otherwise it splits as now, and **closes a branch**
     whose equation contradicts the hypotheses (the `cases` closers:
     two that contradict, after taking `&&`/`||` tests apart as `byFacts`
     phase 1 does) before walking it. The split replaces the scrutinee in
     the hypotheses too, as `match g:` does (D3701), so `noRange:
     rangeAhead modes rest = False` computes under `peekIn modes 0 rest =
     Some kind`. Both help the post families as well (fewer dead branches
     walked), but only exact families need them.
   - **`++` leaves.** The done lemma's `stays: input = rest` and any
     weaken leaf that differ only in how `++` associates are closed by
     the `then` term, `rewrite repeatedly [List.appendAssoc,
     List.appendNil] then byComputing` (existing tools,
     `crates/elab/src/rewrite/repeatedly.rs`); a built-in list leaf closer
     is a later step only if the pilot shows many.
   - Hypotheses and goals in `Runs` need nothing: `Runs` unfolds to
     `RunsOn`, which unification does on its own (§4.1).
3. *docs*: `docs/syntax.md` "byWalking" (exact families, decided splits,
   pruned branches), the proving guide's walk section, and
   `examples/accept/walk-runs*.sw`, `examples/reject/walk-*.sw` for the
   new `E-WALK` message.

**Cost.** std lane (as H): Sonnet, 40 min. Walk lane: Opus (tactic work,
D2506), 50 min. Then the pilot and sweep (§5). **Risk.**
- *Kernel:* nothing new; the walk writes `Parse.runsOnThen` applications,
  `rewrite`s by hypotheses and proof `match`es, which the elaborator
  checks as hand-written ones. `docs/core.md` doesn't change.
- *Terms and hashes:* the std change re-records every hash snapshot;
  converted proofs' terms change. No statement's meaning changes; `Runs`'s
  redefinition is a re-typing checked statement by statement (D2436),
  with an equivalence lemma to the old form to make that easy (§4.1).
- *Check time:* the terms are close to the hand proofs' (same lemma per
  step, fewer written arguments), so the walk's own search is the cost.
  W4b's slowest kept walks came in at 2.4× to 3× their hand proofs and
  every namespace within 1.15× [read, SW-4477 review]; long `Runs` chains (10 to 15 steps)
  and decided-split lookups are the risk to the 3× bar. The pilot
  measures it (§5, stage 3).
- *Scope:* nothing narrows what the formatter accepts or what any top
  theorem says (D3688). A statement that doesn't walk keeps its hand
  proof (in H's shorter form).

**Saves** 2,000 to 2,450 of the 3,242 lines (about 75% of the parser-run
proofs; 82% in the sample, less for the `RunsFrom` and state-using ones)
[estimated]. If SW-4520's `_` pass ran on these files first it would
take about 1,000 of those lines anyway, so E's own share is about 1,000
to 1,450 more. Outside slice 1 the same walk reaches std's own `Runs`
proofs (44 `runsBind`), the toy formatter's (48) and AoC 2020 day 7 and
2021 day 16 (78) [measured], not counted here.

### 3.5 A proof word of its own (`byRunning`)

A second tactic that follows a parser for `Runs` goals would duplicate the
walk's call lookup, splits, leaves and `--expand-walk`, and is new
user-visible syntax (Matt's). E gets the same result inside the existing
`byWalking` by declaring a family. Not recommended.

### 3.6 Side by side

| Option | Walk change | New syntax | Agent time | Lines saved [estimated] | Main risk |
|---|---|---|---|---|---|
| I: implicits on `runs*` | none | no | 30 min (in SW-4520) | 900 to 1,100 | rewritten again later |
| H: `RunsOn` lemmas, hand chains | none | no | 40 + 70 min | 1,700 to 2,000 | low |
| P: post family + substitution | one-run substitution, decided splits | no | 40 + 60 + 70 min | 2,000 to 2,400 | `J` per step, check time |
| **E: exact family on `RunsOn`** | exact binds, decided splits | **no** | 40 + 50 + 35 + 70 min | **2,000 to 2,450** | check time on long chains |
| `byRunning` | a second tactic | yes (Matt's) | 90 min + | as E | duplication |

## 4. Details

### 4.1 `RunsOn`, and `Runs` from it

```
--| `parser`, run on `input` from any honest state, succeeds with `value`
--| and stops with `rest` left, having moved the offset on by what it read.
def Parse.RunsOn (parser: () → {Parse t} a) (input rest: List t) (value: a): Prop :=
  ∀ (state: Parse.State t) => state.at.rest = input
    → state.at.left = state.at.rest.length
    → ∃ (after: Parse.Mark t) => Parse.runFrom state (() => (parser(), Parse.mark())) = Ok (value, after)
      ∧ after.rest = rest
      ∧ after.left = rest.length
      ∧ after.offset + rest.length = state.at.offset + input.length

def Parse.Runs (parser: () → {Parse t} a) (read rest: List t) (value: a): Prop :=
  Parse.RunsOn parser (read ++ rest) rest value
```

The last clause is today's `after.offset = state.at.offset + read.length`
with `input = read ++ rest` (by `List.lengthAppend` and arithmetic): the
same proposition, a different term. A theorem `Parse.runsIff` states the
equivalence with today's definition, word for word, so the re-typing can
be checked once. `RunsOn p input rest v` alone says `rest` is a suffix of
`input`: from the offsets and honesty. The same is done for `RunsFrom`
(`RunsFromOn state …`) so that the lexer's lemmas keep their form.

What migrates: the proofs that open `Runs` or `RunsFrom` (`state starts
honest =>`): 55 in std, 12 in `tools/fmt`, 37 in `tools/toyfmt`, none in
`aoc/` [measured], each changing the offset clause's proof (usually an
`arithmetic` with `List.lengthAppend` added). `runsBind` and the other
`Runs` lemmas keep their statements and are re-proved through `RunsOn`,
so their uses in std, the toy formatter and AoC don't change. Keeping `Runs` with
its own definition and adding bridge lemmas instead would save that
migration but leave two relations, bridges and a walk entry step forever;
by the end state (D2303) the redefinition is better.

### 4.2 What the walk writes, for `runsNegativeNumber`

`negativeAtom self modes` unfolds to `negativeAtomOn self modes left()`:
a bind of `left()`, lemma `runsLeftOn` (`RunsOn left input input input`,
so `v` and `mid` are both `[minus, number, ..rest]`); then
`negativeAtomOn self modes [minus, number, ..rest]`, whose `if
negativeNumeral items` is stuck, decided by `numeral`; then `bump()`
(`runsBump`: `RunsOn bump [item, ..more] more item.leaf.word`, unified with
the input, so `mid = [number, ..rest]`), `left()` again, and a tail
`Prefix … (Atom … (bump()))`: a bind and a done, whose leaves `rest =
rest` and `Prefix … = Prefix …` compute. The chain is the hand proof's,
with `runsOnThen` for `runsBind`/`runsLook`/`runsMap`, and
`--expand-walk` prints it.

### 4.3 What stays by hand

- Proofs that use the state: `mark()` values, `mark().left` fuel, values
  with offsets (`runsAtomAfterPlain`, most of `LexProofs`' `RunsFrom` and
  `ItemReads`). `RunsOn` can't give a mark as a value, since it
  quantifies over states. Stage 5 decides whether a state-indexed exact
  family (`RunsFromOn`, its bind's `∀ middle` with the offset fact) is
  worth it for 58 theorems and 777 lines; H's shorter form applies to
  them either way.
- A proof's own induction (`runsCommaListFrom`'s `match steps`, the fuel
  arithmetic): the arms walk, the `match` stays.
- Look-ahead facts the code's tests don't match one for one (a hypothesis
  about `rangeAhead` against code that tests `kind == DotDot` first):
  closed by pruning if the parts line up, else by `then`.

## 5. Plan

In order. Estimates are agent time. No stage changes what the formatter
accepts or any statement's meaning.

| # | Lane | Model | Estimate | Should save |
|---|---|---|---|---|
| 1 | **std: `RunsOn`.** `Parse.RunsOn`, `RunsFromOn`; `Runs` and `RunsFrom` redefined from them, with `Parse.runsIff`; `runsOnThen`, `runsOnDone`, `runsOnWeaken`, `runsOnMap`, `runsOnSame` and the primitives, implicit where unification fixes them, tagged as in §3.4; `runsBind` and the rest re-proved through them; the 104 proofs that open the definitions migrated; std's API docs; all hash snapshots re-recorded. Check: std's `Parse` namespaces, the two AoC days, `tools/toyfmt`'s touched namespaces, `tools/fmt`'s `Syntax.ReadBackRuns` and `Syntax.LexProofs` | Sonnet | 40 min | 0 itself; H's chains possible from here |
| 2 | **Walk: exact families and decided splits** (§3.4 item 2), with `docs/syntax.md`, the proving guide and accept/reject examples; three `ReadBackRuns` theorems (`runsNegativeNumber`, `runsExprInline`, `runsUnaryPrefix`) converted as the test, with times | Opus | 50 min | about 130 lines in the three |
| 3 | **Pilot: `ReadBackRuns.sw`.** `byWalking` for its `Runs` theorems, H's chains for those that don't walk; times against D3696's bar (no theorem over 3×, the namespace within 1.5×); a list of what stopped the walk | Sonnet | 35 min | 1,100 to 1,350 of its 1,751 lines |
| 4 | **Sweep: the other read-back files** (`ReadBackHung*`, `ReadBackTree`, `ReadBackProofs`), the same way; two lanes by file | Sonnet, or DeepSeek once stage 3 has written the rules | 35 min a lane | 600 to 800 |
| 5 | **`RunsFrom` and `ItemReads`** (lexer): paper first, on whether a state-indexed exact family pays for 58 theorems, else H's chains | Opus (paper), then Sonnet | 20 + 35 min | 300 to 450 |

Total: about 3 h 15 min of lanes, about 2,000 to 2,450 lines
[estimated]. Stage 1 is worth doing whatever Matt decides on the walk: it
is option H's first step, and stages 3 to 5 fall back to H's chains where
the walk stops.

**Sequencing (the orchestrator's call, noted here).** SW-4520 (SW-4519
lane 1, the `_` pilot) is planned on `ReadBackRuns.sw`; if E or H goes
ahead, that file's proofs are rewritten in stage 3, so SW-4520 should
pilot on `ElementsBlank.sw` and a printer file instead, and SW-4519's
lane 5 sweep should leave the read-back files to this plan.

## 6. The decision for Matt

**Adopt option E?** Redefine `Parse.Runs` as `RunsOn p (read ++ rest)
rest value` over a new stop-indexed `Parse.RunsOn` (the same proposition),
and let `byWalking` take a family whose bind lemma fixes the value (an
exact family), deciding a split from a hypothesis instead of walking
every branch. **Recommendation: yes.**

- *The problem:* 179 slice 1 proofs that a parser reads what it should are
  written out step by step by hand, three quarters of their lines
  bookkeeping, because the walk can't follow a completeness statement.
- *The change:* stages 1 to 5 above; no new syntax or attribute, nothing
  in the kernel, no statement's meaning changed. What `byWalking` accepts
  as a family widens, in docs/syntax.md.
- *What it should do:* about 2,000 to 2,450 of those proofs' 3,242 lines
  go, and a typical one is a single `byWalking` line [estimated];
  check time held to D3696's bar, measured in stage 3.

The alternative without the walk change is option H (stage 1, then hand
chains): about 1,700 to 2,000 lines, no tactic work, proofs that still
name every step.

## 7. Findings worth tickets

1. **The walk walks dead branches.** For any family, a branch whose
   equation contradicts a hypothesis could be closed, not walked; and a
   split a hypothesis decides could be one path. Part of stage 2, useful
   beyond `Runs`.
2. **The read-back records are their own 1,691 lines** (26 theorems in
   `ReadBackHung*`), which the walk can't reach: they build `∃` witnesses
   about the printer's output. They belong to SW-4519's kinds A and D, and
   a lane looking at anonymous constructors for their tuples.
3. **`runsLook` and `runsBindEnd`** (`ReadBackRuns.sw`) are std-shaped
   lemmas living in the formatter; with `RunsOn` they disappear
   (`runsOnThen` covers both).
