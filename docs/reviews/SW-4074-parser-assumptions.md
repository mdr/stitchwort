# The parser proofs' assumptions, audited (SW-4074)

Fable, 18 November 2026. Paper: the code read, one script over the
theorem signatures, and one `stitchwort eval`. Nothing was built or
checked again.

How claims are marked: **[source]** read in the code, place given;
**[scan]** from the script (below); **[computed]** the `eval` gave it;
**[inferred]** my reasoning.

## In plain words

**The problem.** SW-4017 found that `FrameRest.others` was false: it
spoke of a `seen` token the parser had read, but let it be any token. So
nothing could ever supply a `FrameRest`, and every theorem that took one
said nothing. The question is whether any other assumption is like that.

**The answer.** None is. Every assumption record in the two parser walks
is now built by a closed definition, so each is true as stated, for
every value of the things it quantifies over. No theorem in
`tools/fmt/src/Fmt/` takes a fact about the parser as a hypothesis. The
source-level theorems' hypotheses hold together on a real file
[computed].

**What is left.** Three things, none a hole in soundness:

1. Four theorems still take a `FrameRest` they no longer need, and the
   two that slice 1 will use (`parseShaped1`, `parseLexical1`) have no
   version stated from the source. Finding 1.
2. Read-back's hypotheses are shown to be satisfiable only by items
   written by hand, not by the items the lexer gives. Finding 2.
3. One read-back rung has the SW-4017 shape (`BlockAt`, over the line's
   kind) but is inhabited. Finding 3.

## What was checked

- **66 named assumptions**: the fields of the nine records, the nine
  `Prop`s that say what a parser function does, the read-back relation
  and its look-ahead records, the lexer's five, and the data hypotheses
  of the top theorems.
- **907 hypothesis binders** in `Syntax/Parse*.sw`, `ReadBack*.sw`,
  `LexReadsProofs.sw` and `GoodItemProofs.sw` whose type mentions one of
  those [scan]. Each is a use of a named assumption or a combinator's
  premise. 44 are `∀`-quantified; I read all 44. Two theorems with such
  a hypothesis are used nowhere (`atMany`, `reads0If`: plain
  combinators, harmless).
- The script matches binders nested two brackets deep, so it misses a
  few deeper ones; the two I know of (`blockLinesOneLine` and
  `blockOneLine`'s `reads`) are in the table.

"Inhabited" below means a closed term of the type exists in the tree,
which the kernel has checked. A proved assumption can't be false, so for
those the SW-4017 question is only whether the statement is the one
meant.

## The table

`self` is the parser's recursive call; `expressionAt` is the real one.
"Free" lists what is quantified over that the parser reads or computes
rather than being told.

### The walks (`ParseWalk`, `ParseCarries*`, `ParseWalkOthers`)

| Assumption | Claims | Free | Inhabited? | Discharged by | Risk |
|---|---|---|---|---|---|
| `Nested self` | `self` gives `GoalParsed` trees at every goal | - | yes | `givesExpressionAt` (`Parse.givesRecursiveWith`) | none |
| `OutsideAtoms` (9 fields) | `matchExpr`, `clauseLambda`, `recordExpr`, `atomRest`, `atomMissing`, `parenOther`, `rightSection`, `annotated`, `namedArgument` give trees outside the slice | `kind` (`rests`); `second`, `third` (`parenOthers`); `keyword`, `open`, `first` | yes | `outsideAtomsOf` | none |
| `OutsideBraced.braceArguments` | `C { … }` arguments are outside | - | yes | `outsideBracedOf` | none |
| `OutsidePiped.pipeChains` | a pipeline gives its operand back or a tree outside | `indent`, `value` | yes | `outsidePipedOf` | none |
| `OutsideCompared` (4) | `membership`, `comparisonChain`, `cmpIf`, `quantifier` are outside | `first`, `kind`, `operator`, `lhs`, `second` | yes | `outsideComparedOf` | none |
| `OutsideIffed` (3) | `iff`, `semiExpr`, `effectResult` are outside | `logic`, `value` | yes | `outsideIffedOf` | none |
| `Outside` (5) | `exprKeyword`, `lambda`, `ifKeyword`, `piExpr` are outside; `statementOther` gives `StatementOk` | `kind` (guarded by `startsKeywordExpr`, `startsOtherStatement`), `implicit` | yes | `outsideOf` | none |
| `AtomBases self` | `atomBase` gives an argument | - | yes | `givesAtomBases` | none |
| `PatternNested pself` | the pattern parser returns (says `True` of the value) | - | yes | `givesPattern` | none |
| `Frame.attributes`, `.namespaces`, `.imports` | attributes return; namespace and import lines are outside | `seen: Seen` | yes | `frameOf` (`givesAttributesOf`, `givesNamespaceStep`, `givesImportStep`) | none |
| `Frame.others` = `FrameRest.others` | `declarationOther` gives a declaration outside the slice | `seen: Option Tok`, `attributes` | yes, since SW-4017 | `frameRest` (`givesDeclarationOther`) | none now; finding 1 |
| `NestedCarries self` | `self` carries its items' words to the tree | - | yes | `expressionAtCarries` | none |
| `NestedBoth self` | both of the above at once, for one knot | - | yes | `bothExpressionAt ladderOf` | none |
| `BasesCarry self` | `atomBase` carries its items | - | yes | `basesCarry` (`readsAtomBases`) | none |
| `Ladder self` (5 fields) | `expr`, `exprInline`, `logicLevel`, `cmpExpr`, `thenBody` carry their items | - | yes | `ladderOf` | none |
| `LadderCarries` | a `Ladder` for every `self` that is `Nested`, carries and has `Outside` | `self` | yes | `ladderOf` | none |
| `GroupCarries frame` | a declaration parsed from a group of good items has the group's words | - (`frame` unused) | yes | `groupCarries` | none; finding 1 |

The fields with free parser-read values (`rests`' `kind`, `parenOthers`'
`second` and `third`, `comparisonChains`' `kind`, `memberships`'
`first`, `others`' `seen`) have the same shape `FrameRest.others` had.
They are true as stated because each walk covers every value, including
the ones the caller never passes [source: `ParseWalk.sw:5709`-`5769`,
`ParseWalkOthers.sw:766`]. `others` became true only because SW-4017
added a guard to `instanceDecl`.

### The top theorems of the walks

| Theorem | Hypotheses | Inhabited together? | Risk |
|---|---|---|---|
| `parseCarriesSourceProved`, `parseSettledSourceProved` (`ParseWalkOthers.sw:770`) | `lex source = Ok lexed`, `alphabet1`, `spelledPlain1`, `plain1`, `parseFile lexed.settledOnce = Ok file`, `file.within1` | yes: `holdsOnExample` has all but `spelledPlain1` [source: `ParseSettledStatements.sw:153`], and `spelledPlain1` is `True` of the same source [computed] | none |
| `parseCarries1`, `parseSettled1`, `parseCarriesSource`, `parseSettledSource` | the same, plus `frame: FrameRest expressionAt`; the first two take `good` (every item `GoodItem`) in place of the source | yes (`frameRest`; `good` from `settledGood`) | low: finding 1 |
| `parseShaped1`, `parseLexical1` (`ParseWalk.sw:6560`) | `frame`, `good`, `parses`, `within` | yes | low: no source-level version exists; finding 1 |

`GoodItem` is false of a qualified name and of a numeral with an
exponent, so these theorems say nothing of a file holding one; that is
known and stated (`qualifiedIsLower`, `exponentIsFloat`), and
`spelledPlain1` is the test that keeps such files out.

### Read-back (`ReadBack*.sw`)

These run the other way: given items of a certain shape, the parser
reads this tree. The assumptions are about the items, and all the items
are quantified freely.

| Assumption | Claims | Free | Inhabited? | Discharged by | Risk |
|---|---|---|---|---|---|
| `SelfRuns sub self bound` | `self` reads every shorter read `sub` holds of | - | yes | `treeStep`, inside `runsTree` | none |
| `Tree goal read rest value` (`Layer`: `FullReads`, `UnaryReads`, `AtomReads` and the rungs under them) | `read` is what the parser at `goal` should read as `value` | the items | yes | `treeWord`, `fullLine`, `fullAnyLine` (`ReadBackLine.sw:1947`) | none |
| `DeclarationTree` (6 fields) | the four frame kinds; the type and value are `Tree`s | the items | yes | built in `readsBackWords` and `readsBackLine` | none |
| `QuietModes` | no guard, `calc` or rewrite rule | - | yes | by computing, for `Modes.start` and the body's modes | none |
| `AtomEnds`, `UnaryEnds`, `OperandEnds`, `EndKind`, `InlinePlain`, `ParenPlain` | look-aheads after or before a node are all false | `head`, `kind` in `UnaryEnds.atom` | yes | `endsAtom`, `unaryEndsOf`, `endsOperandOf`, `endKind`, and the walks in `ReadBackLine` | none |
| `BlockAt`'s `∀ (kind: LineKind)` | the line reads inline in the line modes of every kind | `kind`, which the parser gets by peeking (`lineKindOf seen`) | yes | `fullAnyLine` via `fullOfStarts` | low: finding 3 |
| `blockLinesOneLine`, `blockOneLine`: `reads: ∀ at kind`, `ends` | the statement reads as `line` at every mark with the same rest, in every kind; nothing after continues the block | `kind`, `at` | yes | `runsBlockLine`'s callers | low: finding 3 |
| `runsApp`, `runsOperatorExpr`: `at: ∀ (start: Nat)` | the step runs whatever offset it was started at | `start`, from `offset()` | yes | their callers in `ReadBackRuns` | none |
| `readsBackLine`'s 12 hypotheses (`ReadBackLine.sw:2481`) | four kinds; `Spelt result typeRead`, `Spelt value valueRead`; `lineAll`, `inLineAll`, `laterInLine`; `autoFree1` | every item, with its `index`, `depth`, `glued`, `afterOperand`, `afterDot` | yes, by hand-built items only | **not yet** for the items of a printed file (ticket 17d on) | medium: finding 2 |

`Layer` is `Void` at every level but full, unary and argument. The rungs
call `sub` only at those three [scan: 15, 3 and 8 uses in
`ReadBackTree.sw`], so no rung is closed off by that.

### The lexer (`LexReadsProofs`, `GoodItemProofs`)

| Assumption | Claims | Inhabited? | Discharged by | Risk |
|---|---|---|---|---|
| `Sound p`, `Gives p holds`, `Goes p` | `p` read a start of its input; its value has `holds` | yes | the lexer's walk, ending in `lexLaidProved` and `settledGood`, both closed | none |
| `Yields p holds` | whenever `p` succeeds, `holds` of its value | yes | the text-literal walk | none |
| `Ran p` | nothing: it is `p = p`, there to name a parser for `yieldsThen` | trivially | `ran` | none |

### `Fmt/`

No file in `tools/fmt/src/Fmt/` mentions `FrameRest`, `Parse.Gives`,
`Parse.ReadsIn`, `Nested`, `Outside` or `expressionAt` [scan]. The top
statements of `OutputStatements.sw` and `TriviaStatements.sw` take the
tree's four tests (`within1`, `shaped1`, `settled1`, `lexical1`), and
`hung1` or `DeclHangs`: facts of a tree, not of the parser. `DeclHangs`
has a witness (`atomDeclHangs`) and a derivation in progress
(`DeclFactsProofs.sw`); it is outside this audit.

## Findings

### 1. `FrameRest` is still a parameter, and two theorems have no source-level form

Fifteen theorems take `frame: FrameRest expressionAt` [scan]:
`parseShaped1`, `parseLexical1`, `parseFileOk`, `parseGroupsOk`
(`ParseWalk`); `readsDeclarationBody`, `readsDeclarationKind`,
`readsAtDeclaration`, `runCarries`, `groupCarries`
(`ParseCarriesDecl`); `parseGroupsCarried`, `parseCarriesOf`
(`ParseCarriesFile`); `parseCarries1`, `parseSettled1`,
`parseCarriesSource`, `parseSettledSource` (`ParseSettledStatements`). It is
harmless now, but it is how the vacuity hid: a reader can't tell from
the statement that the hypothesis is met. Also:

- `GroupCarries (frame)` never uses `frame`, and `Frame self` and
  `FrameRest self` never use `self`.
- `parseShaped1` and `parseLexical1` are the two the driver's theorem
  needs for `shaped1` and `lexical1`, and neither has a `…Proved` or a
  from-the-source form, as the other two got in SW-4017.

**Fix.** One Sonnet or DeepSeek lane, about 15 min: remove the `frame`
parameter from all fifteen (use `frameRest` inside, or fold `FrameRest`
into `Frame` and build it whole in one closed `frame`); drop the unused
`self` and `frame` parameters; add `parseShapedSource` and
`parseLexicalSource` with `parseCarriesSourceProved`'s hypotheses. Then
`ParseSettledStatements`' header ("stated and not yet proved") is out of
date and should say so. `frameRest` is defined in `ParseWalkOthers`,
which imports all four of those files, so the lane either moves the file
theorems after it or moves the `declarationOther` walk before them.

### 2. Read-back's witnesses are hand-built items

`readsBackLineExample` and its five siblings apply `readsBackLine` to
`wordItem`s: every item has `depth = 0`, `glued = False`, `afterOperand
= False`, `lineIndent = 0` and its index as its column, also inside
brackets [source: `ReadBackEnds.sw:456`, `ReadBackLine.sw:2575`]. The
real `items` gives depth 1 and 2 there and sets `glued` from the
spacing. The theorem is proved for every item, so this is not a false
assumption. But it is the same blind spot at one remove: nothing yet
shows the hypotheses hold of the items a lexed line has, and `Spelt` is
a `Prop`, so no test can run it. The `ItemsAt` lemmas
(`ReadBackTree.sw:1748` on) are the start of the bridge.

**Fix.** Before 17d's walk is built on it, one witness from real items:
`readsBackLine` applied to `items lexed.leaves` for `lex "def d: A :=
(a, [b])\n"`, the hypotheses by computing. About 10 min, Sonnet, and it
can go in the lane now on SW-4069 if that lane is still open. If a
hypothesis fails there (say `Spelt`'s `glued` conditions for a sign),
that is found now and not at the end of 17d.

### 3. `BlockAt` quantifies over the line's kind

`BlockAt` asks for `InlineAt` in `lineModes … kind` for every `kind`,
and `blockOneLine` takes its statement's reading at every `kind`
[source: `ReadBackTree.sw:601`, `ReadBackProofs.sw:59` and `:104`]. The
parser has one kind, `lineKindOf` of what it peeked. This is the
SW-4017 shape. It is inhabited (`fullAnyLine`), and it can be, because
the kind only goes into `Modes.lines`, which nothing reads but
`Modes.gap`'s `blockEnd` when a recovering body runs out
[source: `Parser.sw:678`, the only use]. So the readings don't depend
on it [inferred].

**Fix.** None needed. If a later rung does come to depend on the kind,
state it at `lineKindOf (Some item.kind)` instead of all four. Worth a
comment on `BlockAt` saying why every kind is satisfiable; the next
lane to touch the file can add it.

### 4. A rule for new assumptions

The vacuity lasted from SW-4000 to SW-4017 because an assumption record
with no witness looks the same as one with. Two cheap habits would have
caught it [inferred]:

- An assumption taken as a hypothesis of a top statement gets a witness
  in the same lane: the record built for one concrete input, or a
  `byComputing` case where its hypotheses hold. `holdsOn` in
  `ParseSettledStatements` is the model.
- A field that speaks of a value the parser reads (`seen`, `kind`,
  `second`) is stated under the test the caller made, as
  `Outside.keywords` is (`startsKeywordExpr kind = True → …`). Then it
  need only be true where it is used.

Both belong in `docs/proving-guide.md`, "Writing statements". That is an
edit to the lanes' instructions, so it is the orchestrator's to place.

## Decisions for Matt

None. Nothing found weakens a statement or narrows the slice.

## How the scan was made

`scan.py` in the lane's scratch folder: for every `theorem` and `def` in
the files named above, the bracketed binders of its signature whose type
mentions `Parse.Gives`, `Parse.ReadsIn`, `Parse.ReadsAt`, `Parse.Runs`,
`Parse.LoopRuns` or one of the named `Prop`s and records; then which of
those theorems' names appear nowhere else, and which binders hold a `∀`.
The `eval`, from `tools/fmt`:

```
stitchwort eval src/Syntax/ParseSettledStatements.sw \
  'match lex "<holdsOnExample's source>" with
     | Err _ => False
     | Ok lexed => Syntax.GoodItemProofs.spelledPlain1 lexed.leaves'
True: Bool
```
