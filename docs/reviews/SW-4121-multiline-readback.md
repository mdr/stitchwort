# Read-back for declarations over several lines: the statement, checked, and the lane plan (SW-4121)

Fable, 19 November 2026. Paper only: no code, proof or test in the repo
was changed. I read the three reviews named in the brief, the parser's
line rule, `Fmt.hangs`, the one-line read-back proofs and the top
theorems; wrote a scratch module (deleted) and a generator; and ran the
proposed statement on generated declarations.

How claims are marked: **[measured]** counted by a run of mine;
**[source]** read in the code or a note, place given; **[estimated]** my
judgement.

## Summary

**The statement.** A declaration's tokens parse back to the tree they
spell, on any number of lines, when the tokens keep the line rule
`Fmt.hangs`. That is today's one-line theorem (`readsBackLineWithin`)
with its two "starts no line" conditions replaced by one: `hangs` of the
group's leaves. Nothing else is needed from the printer, and `hangs` of
the printed leaves is what the driver's proof already has in hand
(`hung1`). The statement is in section 2; the stubs are in section 6.

**How much was checked.** No failure in any check [measured]:

- *The statement itself, without the printer.* 22,000 generated files
  in layouts the printer would never make (random line breaks, random
  columns, comments and blank lines anywhere). 16,207 of them are slice
  1 programs when put on one line. Of those, 11,275 keep `hangs`, 9,096
  of them over several lines, and **every one of the 11,275 parses to
  the same tree as its one-line form**. Of the 4,932 that break
  `hangs`, 2,175 parse to something else or not at all, so the
  condition is doing real work.
- *The printer's side, end to end.* The same files through the driver
  with its one-line test taken out. It accepts 14,032; 11,200 of them
  print over several lines. Every output keeps `hangs`, parses back to
  `calmTop` of the printed tree, and formats to itself.
- 66 hand-written cases for each layout the brief lists, the comment
  between a sign and its operand (D3686) among them: all pass both ways.

**Confidence.** High that the top statement is true: it is the statement
SW-3969 planned, `hangs` has not changed since, and this is the first
time it has been run against the parser on layouts beyond the printer's.
Medium that the lane plan's inner statements are right as first written:
they are stated from reading the proofs, not run. The plan starts with a
skeleton lane that states every inner lemma as an open goal and checks
that they compose, before any is proved.

**Lane plan.** 10 lanes, 13 with the usual growth: one Opus skeleton
lane, four small Sonnet lanes, four lanes that carry the one-line proofs
over (two Opus, two Sonnet first), one Opus lane to assemble. About 3 to
4 hours of lanes running at three at a time [estimated from last
night's lane times]. This piece takes `oneLine1` out of read-back only;
the driver's test goes when piece E (`DeclElements` with comments
anywhere) also lands.

**One thing found.** The one-line theorem holds of any items at all. The
multi-line one does not: the parser's line rule reads each item's index
and bracket depth, so the statement must say the items are a group's own
(`items group`). Section 2 has it as a hypothesis; the printed group
gives it already (`GroupSplit`'s first clause).

## 1. Where the one-line test is used today

[source: `Fmt/TopStatements.sw`, `Fmt/TopReadBack.sw`,
`Fmt/GroupFacts.sw`, `Fmt/GroupSlots.sw` line 914,
`Fmt/SplitProofs.sw` line 43]

| Use | What it buys | Whose piece |
|---|---|---|
| `printedLines1`, then `readsBackLineWithin` | `inLineAll typeRead`, `laterInLine valueRead`: read-back's line facts | **this one (C, D)** |
| `declElementsOneLine1` (`edgeQuietOneLine1`) | the element facts behind `hung1` and `stood1` | E |
| `calmTopOneLine`, `formatsFrom` | the second run passes the driver's test | F: goes with the test |

`printedSplit1`, which gives `Spelt` of the type's and value's items,
takes `PrintedGroup` but throws its one-line clause away (`_` in both
destructurings). So the spelling half of read-back is already proved for
any layout, glue facts included. Only the line facts are missing.

## 2. The statement

`hangs` is `Fmt.hangs` (`Fmt/Predicates1.sw`), unchanged. The new
theorem is `readsBackLineWithin` with three changes:

1. `typeInLine` and `valueLater` go.
2. `hung: hangs group = True` comes in.
3. `isItems: items group = [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]]`
   comes in, because the line rule reads `item.index` and `item.depth`.

```
theorem readsBackHung ∀ (seen: Seen) (group: List Leaf) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (isItems: items group = [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]])
    (hung: hangs group = True)
    (isDef: keyword.kind = KwDef)
    (isLower: name.kind = Lower)
    (isColon: colon.kind = Colon)
    (isColonEq: colonEq.kind = ColonEq)
    (typeSpelt: Spelt result typeRead)
    (valueSpelt: Spelt value valueRead)
    (typeLine: lineAll typeRead = True)
    (valueLine: lineAll valueRead = True)
    (typeWithin: result.within1 = True)
    (valueWithin: value.within1 = True):
    Parse.run (items group) (() =>
      let decl := declaration seen
      decl)
      = Ok (Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value))
```

`PrintedGroup` swaps its sixth clause, `decl.oneLine1 = True`, for
`hangs decl.leaves1 = True`. `readsBackDecl1` keeps its statement
(`PrintedGroup decl read group → DeclReadsBack seen group read`) and is
re-proved from `readsBackHung`. `readsBackFile1`, `fileGroupsRead` and
`groupsReadBack` pass `hung` (which `readsBackFile1` already takes)
where they pass `oneLine`. `outputParses1` has `hung` in hand before it
calls them.

### What comes from where

| Fact | From | State |
|---|---|---|
| `hangs decl.leaves1` | the printer: `printedHangs1`, given `DeclElements` | proved for one-line declarations; any comments is piece E |
| `tokens group = tokens decl.leaves1` | rule N on the output keeps tokens (`settledKeepsTokens`) | proved, in `PrintedGroup` |
| `hangs group` | the two above: `hangs` reads tokens only | one small lemma, H1 below |
| `isItems`, the kinds, `Spelt`, `within1` | `printedSplit1` | proved, for any layout |
| `lineAll` | `speltExpr`, `exprLine` | proved (the part of `printedLines1` that stays) |
| the parse | the parser's relation `Tree` and `declarationTree` (`Syntax/ReadBackTree.sw`), which already has the block case (`BlockAt`, `runsBlockTree`) | proved; what is missing is building `Tree` from `Spelt` and `hangs` |

Not needed by read-back: `stood1`, `DeclHangs`, `unreturned1`. They
feed `printedSettle1` (the words rule N gives back), which is proved
and has no one-line condition.

Comments need nothing of their own here. Items carry no comments; a
comment only makes the next token start a line, and `hangs` covers
where it then stands. Where rule N has moved a comment, the tokens are
the same.

### Why `hangs` is enough

The parser looks at line starts in three places on slice 1's paths
[source: `Syntax/Parser.sw` lines 235 to 242, 637 to 660, 780 to 788]:

| Parser test | When it fires | The `hangs` clause that keeps it quiet |
|---|---|---|
| `startsBlock`, in `expr`: the first item of a type, a value or a bracket's item starts a line. A block opens at its column, and that column becomes the limit | every such item | `start` and `fresh`: the same column is recorded, in `top` or at the head of `blocks` |
| `stopsByLine`: an item starts a line at or left of the limit, and is no comma or closer inside a bracket | would end the expression early | "a leaf that starts a line is right of the column in force"; no comma starts a line |
| `blockOffset`: after a block's line, the next item starts a line at exactly the block's column | would start a second statement | a closer that starts a line is left of its item's column; `:=` ends blocks |

The operand of `->` is read by `expr` too, and `hangs` records no
column for it. The `glue` clause closes that: the leaf after `->` may
not start a line, so no block opens there [source: SW-3969's notes].

## 3. What `readsBackLineWithin` handles today that must generalise

[source: `Syntax/ReadBackLine.sw`; counts by grep]

| # | Today | With several lines |
|---|---|---|
| O1 | `quietStops`: an item that starts no line never stops a reading. Used at 45 places, each from a piece of `inLineAll` | `hungStops`: an item the line rule steps over doesn't stop, under modes whose limit is no further right than the column in force. The one exception is O5 |
| O2 | `fullLine`: a bracket's item starts no line, so `expr` reads it inline (`fullOfInline`) | either inline, or a one-line block at the item's column: `fullOfStarts`, as `fullAnyLine` does today for the value alone. The block's three conditions (`BlockAt`) come from `hangs`: right of the limit; what follows doesn't continue the block (`stepInBracket`, `stepAtTop`, proved); the line read under the block's modes, whose limit is the item's column |
| O3 | `inLineSplit`, `lineSplit`: "starts no line" splits over `++` with no state | `hangsAppend` (proved) splits `hangs`, but the state must be carried: what it is after a sub-expression's leaves. That is the frame lemma `speltHangs`, new |
| O4 | `QuietModes` is all the lemmas ask of the modes | also `bounds modes state`: the modes' limit is at most the line rule's column in force. An inequality, so it survives both of O2's cases |
| O5 | `restOpen`: the item after the expression doesn't stop. True on one line | false of a `:=` that starts a line at or left of a type that began its own line. Measured: 678 of the passing cases have it. `restOpen` is used in one place, `endsAtom`, for a peek that is `None` when the item stops, so the hypothesis can go |
| O6 | any items: no lemma reads `index` or `depth` | closers and commas need `depth > 0` to be exempt from `stopsByLine`: `hungDeep`, new, from `items group` and `hangs` |
| O7 | the type on the `def`'s line (`fullLine` at `Modes.start`); the value on it or the next (`fullAnyLine`) | both by the one rule, `fullHung`; the header's own line starts (name, `:`, comments above them) are steps of `hangs` from `HangState.initial` |

The parser's relation (`Tree`, `FullReads`, `BlockAt`, `InlineAt` and
the `runs…Tree` theorems, `declarationTree`) needs no change. Nor do
`Spelt`, the look-ahead lemmas of `ReadBackEnds` and `ReadBackRuns`
(they read kinds and `stops`, and go through `peekEnds` both ways), or
the glue lemmas.

## 4. The checks

All runs: the release binary, `nice -n 19`, one at a time, on a scratch
module in `tools/fmt/src` (deleted before the commit). The first runs
used `stitchwort eval`; at 75 s for 250 cases it was too slow for
thousands, so the rest used `stitchwort run` of the same module's two
functions on the fast runtime (4 s for 250), which agreed with `eval`
on the chunks run both ways.

### The generator

A Python script (lane scratch folder, `gen.py`) makes one or two
`def name: Type := value` declarations from slice 1's grammar: names,
numerals, floats, brackets, tuples, lists (empty too), calls, glued and
spaced `-` and `!`, the binary operators at every level, `->` and `→`,
`≤`. It then lays the tokens out with random line breaks, comments
after tokens, own-line comments above tokens and blank lines. It
carries a port of `HangState` to choose columns. Five modes, 250 files
a chunk:

| Mode | Files | What it is for |
|---|---|---|
| wild | 10,000 | a share of line starts at any column, to get layouts that break the rule |
| legal | 5,000 | columns the port allows: many layouts that keep it |
| long | 2,000 | long names on few lines, so the printer must break at 120 columns |
| noted | 3,000 | comments on most breaks |
| longnoted | 2,000 | both |

### Check B: the statement without the printer

For each file: lex it, apply rule N as the driver does, split into
groups. `hung` is `hangs` of every group. The "tree spelt" is found
without a second parser: write each group's tokens on one line, glued
where they were glued, and parse that. `readsBackLineWithin` (proved)
says that parse is the tree the tokens spell. The statement then
predicts: if `hung`, the layout parses, to the same tree (compared by
the dump of `meaning`, which has no comments or blank-line marks).

| Outcome | Files [measured] |
|---|---|
| one-line form is no slice 1 program (generator's misses) | 5,793 |
| `hangs`, several lines, same tree | 9,096 |
| `hangs`, one line, same tree | 2,179 |
| **`hangs`, and a different tree or no parse** | **0** |
| breaks `hangs`, same tree anyway | 2,757 |
| breaks `hangs`, doesn't parse | 2,119 |
| breaks `hangs`, parses to another tree | 56 |

So `hangs` is sufficient on every case, and not necessary (the parser
forgives more than it asks, for example a closer right of its item).
That is the right way round for a condition the printer has to meet.

What the 9,096 multi-line passing files contain (a file counts once
per row) [measured, by a rough scan of the text]:

| Layout | Files |
|---|---|
| a trailing comment inside the declaration | 7,494 |
| an operator starting a line | 5,756 |
| a blank line inside or between | 4,779 |
| an own-line comment inside | 4,557 |
| a line start right after `-` or `!` (sign or minus) | 3,920 |
| a closer starting a line | 3,180 |
| a bracket's item starting a line after its opener | 3,149 |
| `:` starting a line | 2,929 |
| `:=` starting a line | 2,922 |
| the value starting a line | 2,899 |
| a bracket's item starting a line after a comma | 2,020 |
| a comment between `-` or `!` and what follows | 1,973 |
| the type starting a line | 1,266 |
| the type starting a line and `:=` starting a later one (O5) | 678 |

No passing file has a line start right after `->`: `hangs` refuses it.

### Check A: the printer's side

For each file: the driver's steps with the one-line test left out
(lex, `leavesWithin1`, parse from `settledOnce`, `within1`, `tidy1`).
For an accepted file, seven tests of the tidied tree `file`:

1. the tree facts the top proof has (`shaped1`, `settled1`, `lexical1`,
   `commaFree`, both `unreturned1`);
2. `file.hung1`;
3. `file.stood1`;
4. the printed text lexes to `file.lexed1`;
5. `hangs` of each group of `file.lexed1.settledOnce` (what
   `readsBackHung` takes);
6. `readsBack file.lexed1 file`: the output's parse is `calmTop` of the
   tree (`OutputStatements.readsBack`: words, end, dump and printed
   text equal);
7. formatting the printed text again gives it back.

| Outcome | Files [measured] |
|---|---|
| not accepted: doesn't parse (the 5,793 that are no program, and the 2,119 layouts check B found unparseable) | 7,912 |
| not accepted: the layout parses to a tree outside `within1` (check B's 56) | 56 |
| accepted, prints over several lines, all seven tests pass | 11,200 |
| accepted, prints on one line, all seven pass | 2,832 |
| **accepted, and any test fails** | **0** |

The 14,032 accepted files are exactly check B's "same tree" files, as
they should be. Of the 11,200 multi-line outputs, 2,817 come from the
two long-name modes, where the printer breaks for width and not only
for a comment (1,455 with no comments at all).

Tests 2 and 3 are piece E's conclusions (`hung1`, `stood1`), not this
piece's; they are here because a multi-line output that failed them
would sink the plan from the other side. None did.

### Hand-written cases

66 sources, one or more for each layout in the brief (lane scratch
folder, `hand.py`): calls, lists, tuples, operator chains and arrows
too long for a line; comments after and above inner tokens, openers,
commas, closers, `:`, `:=`, `->`, the name; a comment between a sign
and its operand in a bracket, at the start of a value, after a binary
operator, in a type, twice in a row, before a call and before a tuple
(D3686); blank lines in lists, calls, after `:=` and after an
operator; nests four deep.

Check A: all 66 accepted, 58 printing over several lines, all seven
tests pass on each. Check B: 64 keep `hangs` and parse to the same
tree. The other two are sources with a comment right after `->`; the
source breaks the `glue` clause (the next token starts a line), parses
to the same tree anyway, and the printed output keeps `hangs` because
rule N moves the comment [measured].

### What the checks don't cover

- The inner statements of section 6 were not run, only the top one.
- The generator has no `¬`, `∧`, `∨`, `=` or `*`-family unicode forms
  beyond `→` and `≤`, and no name longer than 30 characters.
- "Same tree" in check B is by `meaning`'s dump, so it compares shape
  and tokens, not which token each comment sits on. Check A's test 6
  compares words, comments included, for printed output.
- A check is not a proof: 11,275 cases with no counterexample.

## 5. The lane plan

Lane times for read-back on 18 November: 25, 38, 49, 55 and 63
minutes, and two long ones, 182 and 250 [source: the stock take,
section 5]; the operator lane after it, SW-4071, took 36 [source: its
board note]. Estimates below are from those. Models by D3682.

### The route

Keep the parser's relation and `Spelt`. Carry `hangs`' own state
through the lemmas that build `Tree` from `Spelt`, in place of
`inLineAll`. Each lemma of the one-line family takes the state before
its first item and `hangsFrom` of its items and what follows; splits
use `hangsAppend` and the frame lemma. The alternative, a second
tree-shaped layout relation beside `Spelt`, would have to be proved of
the printer as well, and `hangs` already is.

The proofs go in new files (`Syntax/ReadBackHung*.sw`), one per layer,
so that lanes can run side by side; `ReadBackLine.sw` is 6,616 lines in
one file. When the last lands, the one-line lemmas that have a hung
twin are deleted and their witnesses re-pointed: one family at the end,
not two.

### Lanes

| # | What | Model | Minutes [estimated] | After | Beside |
|---|---|---|---|---|---|
| H0 | **Skeleton.** `Syntax/ReadBackHung.sw`: the definitions of section 6, every lemma of H1 to H8 stated as an open goal, `readsBackHung` proved from them, `PrintedGroup` and `TopReadBack` rewired so the top theorems still check. Three witnesses from the lexer's own items by `byComputing` (a list broken after its opener, `(- -- c⏎ 1)`, a type on its own line with `:=` on the next), so no statement is vacuous | Opus | 60 | - | - |
| H1 | `hangsTokens`: equal tokens, equal `hangs`. `hungDeep`: in a group that hangs, every closer and comma item has `depth > 0` (walk the leaves with `ItemsAt` and `HangState` together; `blocks.length` is the depth) | Sonnet | 30 | H0 | H2 to H8 |
| H2 | `hungStops` and the three `bounds` lemmas (after the first leaf, into a block, into a bracket) | Sonnet | 25 | H0 | all |
| H3 | `speltHangs`, with its list forms for `SpeltSteps` and `SpeltArgs`: the frame. An induction over `Spelt`'s eight forms; `HangState.step` by cases | Sonnet, Opus if stuck | 50 | H0 | all |
| H4 | `endsAtom`, `unaryEndsOf`, `endsAtOf` without `restOpen` (O5) | Sonnet | 20 | - | all |
| H5 | Atoms, brackets and their items: `atomHung`, `tupleSteps`, `listSteps`, `openSteps`, and `fullHung` with the block case. The one place a block opens, so the one hard invariant | Opus | 75 | H0 | H6 to H8 |
| H6 | Calls and signs: `argumentLine`, `argsLine`, `appLine`, `headLine`, `appAny`, `signArgLine`, `unaryLine` | Opus | 60 | H0 | H5, H7, H8 |
| H7 | The chains: `mulLine`, `addLine`, `appendLine`, `cmpLine` and their `Acc` and `Base` lemmas. A walk: each is the one-line proof with `quietStops` and the splits swapped | Sonnet | 60 | H0 | H5, H6, H8 |
| H8 | `&&` and `\|\|`, `->`, `operatorLine`, `inlineLine`. `arrowLine` is where `glue` is used | Sonnet for logic, Opus for the arrow: one lane, Opus | 60 | H0 | H5 to H7 |
| H9 | Assemble: close what is left in `readsBackHung` (the header's steps, the type and value by `fullHung`), delete the one-line twins, audit | Opus | 45 | all | - |

**Order.** H0 alone. Then H1 to H8 in any order, three at a time; H4
can start with H0. Then H9.

**Totals** [estimated]: 10 lanes, about 8 lane-hours; at three build
lanes, about 3 hours on the clock. With the 1.3 growth the stock take's
counts showed: 13 lanes, about 4 hours. SW-4119 put this piece at 4 to
7 lanes; I count more lanes, each smaller, because the work splits by
layer once the skeleton fixes the statements.

**After it.** `oneLine1` is still in the driver, in `Formats1` and in
`declElementsOneLine1`. Piece E replaces the last; piece F then removes
the test and `calmTopOneLine`.

### Risks

- **An inner statement is wrong as first written** (medium). The
  likeliest places: where exactly the state is taken (before or after a
  lemma's first item), and `bounds` across a bracket's close. H0 is
  there to find this before four lanes build on it: it must compose,
  and its witnesses must compute.
- **The frame lemma's bookkeeping** (low to medium). `Spelt` is nested
  existentials; H3 may need Opus.
- **A layout the generator never made** (low). Section 4 lists what it
  left out.

### Stop rules

- H0 can't state the lemmas so that `readsBackHung` follows and the
  three witnesses compute: stop, back to Fable with what broke.
- Two of H5 to H8 report a false statement: stop the rest, back to
  Fable (SW-4119's rule).
- 13 lanes or 4 hours without H9 merged: stop and report.

## 6. Stub statements

For H0 to turn into code. Names are suggestions; the shapes are what
matters. `QuietModes`, `Spelt`, `lineAll`, `endsHere`, `FullReads`, `TreeN`
are as in `Syntax/ReadBackLine.sw` and `Syntax/ReadBackTree.sw`.

```
namespace Syntax.ReadBackHung

--| The leaves of items.
def leavesOf (read: List Item): List Leaf := read.map (item => item.leaf)

--| Every closer and comma is inside a bracket, where `stopsByLine` lets it start a line.
def deepAll: List Item → Bool
  | [] => True
  | [item, ..rest] => (!(item.kind == Comma || item.kind.isCloser) || item.depth > 0) && deepAll rest

--| The parser's block column is no further right than the line rule's column in force.
def bounds (modes: Modes) (state: HangState): Bool := match modes.limit with
  | Some limit => limit <= inForce state.blocks state.top
  | None => True

--| The state an expression is read under once its first leaf has placed it: the column recorded if that leaf
--| starts the expression and its line; no longer at a start, nor after `->`.
def HangState.entered (state: HangState) (first: Leaf): HangState :=
  let fresh := state.start && first.token.lineStart
  {
    blocks = startBlocks fresh first.token.column state.blocks,
    top = startTop fresh first.token.column state.blocks state.top,
    start = False,
    glue = False
  }

-- H1.

theorem hangsTokens ∀ (first second: List Leaf) (same: tokens first = tokens second): hangs first = hangs second

theorem hungDeep ∀ (group: List Leaf) (hung: hangs group = True): deepAll (items group) = True

-- H2.

--| An item the line rule steps over doesn't stop a reading whose limit the rule bounds. A `:=` outside brackets is
--| the exception: the rule lets it start a line anywhere.
theorem hungStops ∀ (modes: Modes) (state next: HangState) (item: Item)
    (quiet: QuietModes modes)
    (bound: bounds modes state = True)
    (stepped: state.step item.leaf = Some next)
    (deep: deepAll [item] = True)
    (inside: (item.kind == ColonEq) = False):
    modes.stops item = False

--| After an expression's first leaf, the bound holds of the state it left.
theorem boundsPast ∀ (modes: Modes) (state next: HangState) (item: Item)
    (bound: bounds modes (state.entered item.leaf) = True)
    (stepped: state.step item.leaf = Some next)
    (plain: (item.kind == Comma || item.kind.isCloser || item.kind == ColonEq || item.kind == Colon) = False):
    bounds modes next = True

--| A block opened at an item that starts its expression and its line bounds the state that item enters.
theorem boundsBlock ∀ (modes: Modes) (state: HangState) (item: Item) (allow: Option Nat) (kind: LineKind)
    (starts: state.start = True)
    (lineStart: item.leaf.token.lineStart = True):
    bounds
      (lineModes (blockModes modes item.leaf.token.column True) item.leaf.token.column True allow kind)
      (state.entered item.leaf)
      = True

--| The same item is right of the limit: `BlockAt`'s first clause.
theorem rightOfBound ∀ (modes: Modes) (state next: HangState) (item: Item)
    (bound: bounds modes state = True)
    (stepped: state.step item.leaf = Some next)
    (lineStart: item.leaf.token.lineStart = True)
    (opens: leadKind item.kind = True):
    rightOfLimit item.leaf.token.column modes.limit = True

-- H3.

--| The frame: the line rule's state after a spelt expression's leaves is the state its first leaf entered.
theorem speltHangs ∀ (expr: Expr) (first: Item) (more: List Item) (state next: HangState)
    (spelt: Spelt expr [first, ..more])
    (after: state.after (leavesOf [first, ..more]) = Some next):
    next = state.entered first.leaf

-- H4: `endsAtom`, `unaryEndsOf` and `endsAtOf` as they are, without `restOpen`.

-- H5 to H8. The pattern, shown on the two rungs that differ most from today's.

--| What `expr` reads, on any lines: a spelt expression at the start of a type, a value or a bracket's item
--| (`state.start`), or after `->` (`state.glue`), whose leaves and what follows keep the line rule. Inline where its
--| first item starts no block; else a one-line block at that item's column.
theorem fullHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (read rest: List Item) (depth: Nat) (state: HangState)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr read)
    (free: expr.autoFree1 = True)
    (lineRead: lineAll read = True)
    (lineRest: lineAll rest = True)
    (placed: state.start = True ∨ state.glue = True)
    (bound: bounds modes state = True)
    (hung: hangsFrom state (leavesOf (read ++ rest)) = True)
    (deepItems: deepAll (read ++ rest) = True)
    (ends: endsHere rest = True):
    FullReads (TreeN depth) modes read rest expr

--| The rungs below `expr` (`inlineLine`, `operatorLine`, the chains, `unaryLine`, `appLine`, `atomLine`): today's
--| statement with `inLater` and `restOpen` replaced by the state before the first item, the bound against the state
--| that item enters, and the line rule over the items and what follows. `open` stays: the first item is the caller's
--| to place (a block's own first item is allowed by its modes, not by its column).
theorem inlineHung ∀ (modes: Modes)
    (quiet: QuietModes modes)
    (expr: Expr) (item: Item) (more rest: List Item) (depth: Nat) (state: HangState)
    (deep: expr.nest1 <= depth)
    (spelt: Spelt expr [item, ..more])
    (free: expr.autoFree1 = True)
    (lineRead: lineAll [item, ..more] = True)
    (lineRest: lineAll rest = True)
    (open: modes.stops item = False)
    (bound: bounds modes (state.entered item.leaf) = True)
    (hung: hangsFrom state (leavesOf ([item, ..more] ++ rest)) = True)
    (deepItems: deepAll ([item, ..more] ++ rest) = True)
    (ends: endsHere rest = True):
    InlineAt (TreeN depth) modes item more rest expr

-- H9, and H0's target.

theorem readsBackHung ∀ (seen: Seen) (group: List Leaf) (keyword name colon colonEq: Item)
    (typeRead valueRead: List Item) (result value: Expr)
    (isItems: items group = [keyword, name, colon, ..typeRead ++ [colonEq, ..valueRead]])
    (hung: hangs group = True)
    (isDef: keyword.kind = KwDef)
    (isLower: name.kind = Lower)
    (isColon: colon.kind = Colon)
    (isColonEq: colonEq.kind = ColonEq)
    (typeSpelt: Spelt result typeRead)
    (valueSpelt: Spelt value valueRead)
    (typeLine: lineAll typeRead = True)
    (valueLine: lineAll valueRead = True)
    (typeWithin: result.within1 = True)
    (valueWithin: value.within1 = True):
    Parse.run (items group) (() =>
      let decl := declaration seen
      decl)
      = Ok (Definition [] (plainHeader keyword name colon result) (Assigned colonEq.leaf.word.comments value))

-- In `Fmt.GroupFacts`: `PrintedGroup`'s sixth clause becomes `hangs decl.leaves1 = True`.
-- In `Fmt.TopReadBack`: `readsBackDecl1`, statement unchanged, from `printedSplit1`, `hangsTokens` and
-- `readsBackHung`; `LinesRead` keeps its two `lineAll` clauses.
```

Notes on the stubs:

- `fullHung`'s `placed` matters. If an expression's first item started
  a line where the line rule records no column, the parser would open
  a block the rule knows nothing of. The two cases are all there are:
  `start` is set after an opener, a comma, `:` and `:=`, which are the
  places `expr` is called; after `->` the rule forbids the line start.
- `bounds` is an inequality on purpose. When the first item of a
  bracket's item starts a line but opens no block (the parser's
  `allow`), the rule has still recorded its column; the modes' limit is
  then left of the rule's, and everything still holds.
- In `fullHung`'s block case the block's own line is read by
  `inlineHung` under the block's modes: `open` from `allow` (as
  `fullAnyLine` has it today), `bound` by `boundsBlock`.
- The type's `rest` is `[colonEq, ..valueRead]`, and `hungStops`
  doesn't cover a `:=`. With H4 no lemma asks it to.

## Findings worth tickets

- `stitchwort eval` of a function over 250 short sources took 75 s; the
  same through `stitchwort run` took 4 s [measured]. A note in the
  proving guide would save the next checking lane the detour.
- The generator written here (`gen.py`: layouts that are not the
  printer's, with a `HangState` port) and the two check functions could
  join `tools/fmt/dev` as a rerunnable gate for H0 to H9. They are in
  the lane's scratch folder, which is deleted with the worktree.
- The header of `Fmt/GroupFacts.sw` and `Fmt/TopReadBack.sw` say
  "one-line"; they will want rewording with H0.

## Sources

- `tools/fmt/src/Syntax/Parser.sw` (`Modes.stopsByLine`, `startsBlock`,
  `exprBlock`, `block`, `blockOffset`, `itemsAfter`);
  `Syntax/ReadBackLine.sw`, `ReadBackTree.sw`, `ReadBackProofs.sw`,
  `ReadBackEnds.sw`; `Fmt/Predicates1.sw` (`hangs`); `Fmt/Driver1.sw`,
  `TopStatements.sw`, `TopReadBack.sw`, `GroupFacts.sw`,
  `GroupSlots.sw`, `SplitProofs.sw`, `PrintedLines.sw`,
  `OutputStatements.sw`.
- `docs/reviews/SW-4119-slice1-review.md`,
  `SW-4078-slice1-stock-take.md`, `SW-4096-one-line-elements.md`;
  `tools/fmt/NOTES.md` (ticket 17); `board show` SW-3969, SW-4013,
  SW-4071.
- Runs: `stitchwort eval` and `stitchwort run` of a scratch module's
  `checkA` and `checkB` over 88 chunks of 250 generated files and 66
  hand-written ones.
