# The direct proof, top-down: what is left (SW-3418, D3620)

Part 14 of "Proving the printer directly" (`NOTES.md`). Fable, 15 Nov
2026. No theorem of the proof itself was proved in this part: it states
the rest, from the goal down, and checks that the statements fit.

## What is checked

`sketch/src/Sketch.sw` (namespace `Toy.Sketch`) defines `formatDirect`
(parse, print, no check of any kind) and proves, from its open lemmas
(five when written, four after lane 2, one after lane 3, none after lane 4) and what `src/` has proved:

| Theorem | Says |
|---|---|
| `printParses` | `parse source = Ok file` gives `parse (file.print width).text = Ok file`, at every width |
| `formatDirectAnswers` | a source that parses gets `Stable (tree.print width)`; only the parser refuses |
| `formatDirectRoundTrip` | the output is the tree printed, and parses to that tree |
| `formatDirectIdempotent` | `formatDirect output.text width = Stable output` |
| `formatAgrees` | `format source width = formatDirect source width`: the run-time check never fails, so every theorem about `format` (the file loop's too) is `formatDirect`'s |

`stitchwort check` in `sketch/` passes with "5 goals open"; `stitchwort
goal` lists them and which theorems rely on each. Idempotence, the
round trip and `formatAgrees` need nothing beyond `printParses`.

**How main stays green.** `sketch/` is a project of its own
(`check: open-goals: warn`), so `Toy`'s `check`, `test` and `audit` never
see a `?`; nothing under `src/` changed. A project's sources must be
inside its folder, so `sketch/toy` is a symlink to `../src`. If a
repo-wide tool follows symlinks and counts `Toy` twice, replace the link
with a copy step or move the sketch; nothing else depends on it.

## The open goals

Counts are lemmas [estimated], sized against files that did the same
kind of work in parts 1 to 13 (named in each row). Risk: routine (the
same shape was proved before), uncertain (new shape, or a statement
that must change first), unknown (not stated precisely).

| Goal | Layer | In words | Needs | Lemmas | Risk |
|---|---|---|---|---|---|
| E1 `placedOffsets` | E | the printed tokens' offsets grow, so no two tokens share one | `placed`, `charsLength` | 5 | routine |
| D1 `parseHeaded` | D (WF) | every parsed file is `HeadedFile`: outside brackets no statement's, declaration's or one-expression body's first token has comments above it (facts a, b); inside brackets every body is one expression (c); no body or file keeps a blank line above its first line (d, new here) | `Parse.Reads`, std `readsOperatorsLeft`, a lexer fact (a token that doesn't start its line has nothing above it) | 75-85 (`ShapeProofs.sw` has 67 for a value-only walk; this one also follows the tokens read), or 25-30 with the program change below | uncertain |
| D2 `runsFileSpelled` | D | the parser reads back what spells a file (`SpelledFile`, defined in the sketch as `SpelledLines` at column 0) | `runsValueSpelled`, `runsFunctionSpelled`, `runsSourceFile` | 12-15 (`linesRun` and its helpers were 6) | routine |
| D3 `runsBodyNested` | D | `body`, read with the expression parser of the induction, reads back a block: an `if` with a block branch | `linesRun` and `runsBodySpelled` restated over `self` with `ReadsNested`; `Spelled`'s `If` arm changed (below) | 20-30 | uncertain |
| D4 (statement change, below) | D | a block may be followed by `then` or `else` at its own column | `statementDeclines` for a keyword; `SpelledLines`' end condition; `linesRun`'s last case | 8-12 | uncertain |
| E2 `spellsFile` | E | tokens whose views are those of a trace of `FileEvents file`, with distinct offsets, spell the file | all of the above as hypotheses; `viewsOf`, `Events`, `eventsFree`, `bodyFree` | 70-90 (below); 56 proved in part 15, 40-45 left | uncertain for blocks, routine for the rest |
| Glue | | move `formatDirect` and its five theorems into `Toy.Fmt`, the driver calls it, the file-loop theorems restated for it | proved in the sketch | 8-13 | routine |

**Total: 200-250 lemmas** (155-195 with the program change).

E2 is counted from its parts, not from part 13's 25-35, which was a
guess before the statement existed: a token's kind from its word (10);
`viewsOf` over `Then` and `TokenAt`, with the comments above and after
as `Layout.comments` gives them (10); `Layout.allows` and `allowsElse`
from the zone's starts and the distinct offsets (6); comment lines and
blank lines back through `spacedNotes` and `notedStatement` (8); the
induction over the ten expression forms and items (14); bodies, lines,
statements (10); `EndsExpression` after each expression and
`blockAhead` at each body (9); declarations and parameters (8);
newest-first lists against source order (5).

## Statements that must change

Two definitions in `src/` are too narrow for E2 to be true of every
file. The sketch's text stays as it is when they widen; D2 and
`printParses` don't change.

1. **`Spelled`'s `If` arm asks `SpelledInline` of both branches**
   (`ExpressionProofs.sw`), so no tokens spell an `if` with a block
   branch outside brackets, and E2 is false of such a file today. The
   arm must ask `SpelledBody`, which makes `Spelled`, `SpelledBody` and
   `SpelledLines` mutual and moves them into one file; `runsIfSpelled`
   then goes by D3. Parts 12 and 13 list it as "`if` with a block branch".
2. **`SpelledLines` ends a block with `lineAhead column rest = False`**
   (no token starts a line at the block's column). New finding.
   `Events` lets the `else` after a block branch start a line anywhere
   no shallower than the statement (`zone.reaches`), and the `then`
   after a condition that is an `if` ending in a block anywhere deeper
   (`zone.allows`); the block's column is only `zone.under`, so a trace
   of `FileEvents` may put either keyword at the block's column, and
   E2 is false of it. Two ways out: (i) weaken the end condition to
   "or the next token is `then` or `else`" and prove `statement`
   declines there (D4; the parser does: the two tests in
   `sketch/src/Probes.sw` pass); (ii) say in `Events` where the keyword
   is against the block's column, which reopens `EventProofs.sw`'s `if`
   lemmas. (i) is the estimate above and holds whatever the rules do.

## Suspected, not stated precisely

- **Inside E2 (unknown).** `viewsOf` is a fold with a state (the trivia
  waiting) over a flat trace; `FileEvents` is nested `Then`s. The
  induction needs one invariant for "the views of a part of the trace,
  from a state": nothing waits at a token, comment lines and one blank
  line may wait at a line start. I didn't state it; if it is awkward,
  E2 grows by 10-20.
- **`HeadedFile` may need one more clause (unknown).** It was written
  from `Parser.sw` and `SpelledLines`, not from a proof of E2. Fact (d)
  was found this way, by reading; another may be there.
- **The parameters (routine).** `SpelledDeclarations` asks for the
  parameter parser's `Runs` directly, so E2 has to build it from views
  (`runsParameters`, `runsNoParameters`); counted in E2's 8.

## After lane 1 (part 15): expressions are spelled

`src/Toy/Fmt/SpellProofs.sw` (56 theorems, in `Toy`'s audit) proves E2
for expressions; `spellsFile` is still open for what is around them.

| Part of E2 | Estimated | Proved | Theorems |
|---|---|---|---|
| a token's kind from its word | 10 | 10 | `codeEvent`, `nameEvent`, `digitsEvent`, `stringEvent`, `keywordEvent`, `signEvent`, `operatorEvent`, `ownLineEvent`, `trailingEvent`, `commentNoBreak` |
| `viewsOf` over `Then` and `TokenAt` | 10 | 5 | `Seen` (the invariant: views in source order, nothing left waiting), `seenThen`, `tokenSeen`, `aboveViews`, `viewsAppend`, `waitingReverse` |
| a token fits its layout (`allows`, `allowsElse`, `comments`, offsets) | 6 | 23 | `innerFits`, `firstLeads`, `reachesElse`, `risingApart`, `Leads`, `headFits`, `innerLeads` and helpers |
| tokens taken apart as their views are | 0 | 5 | `viewsCons`, `viewsSplit`, `viewsOne`, `viewsNil`, `consViews` |
| the induction, inline bodies, a statement that is an expression | 14 + part of 10 | 13 | `exprSpells`, `itemsSpell`, `bodySpells`, `inlineSpells`, `bareSpells`, `spellsBracketed` |
| `EndsExpression` after each expression | part of 9 | 0 | not started |

What `exprSpells` covers: every expression inside brackets (`if`
included, its branches by `bodyFree`), and outside brackets every
expression with no `if` (`Covered`), at the statement's first token
(`bareSpells`) or after it. The suspected invariant ("inside E2,
unknown") is `Seen pending events views` and was not awkward.

Found inside E2, and handled there:

- **The views can't depend on where the statement starts.** The layout
  holds the offset of the statement's first token, which is one of the
  tokens being spelled, so the induction gives the views first and
  spells at every offset (`restart`).
- **The induction has to say how the first view starts**, for
  `blockAhead` at a body on its keyword's line (`inlineAhead`).
- **`Shaped` is needed** (the last item's comma holds no comments,
  `BareLastItem`); `spellsFile` already takes `ShapedFile`.

Found, and outside E2 (read from the definitions; not proved):

- **Statement change 1 is larger than "ask `SpelledBody`".**
  `SpelledBody` takes the tokens after the body, and a block's end is a
  fact about them (`lineAhead column rest = False`, and
  `EndsExpression` at the last line's layout). `Spelled` has no `rest`,
  and `runsIfSpelled` gets only `EndsExpression layout rest`, which
  says nothing of the `else` block's column. So either `Spelled` takes
  `rest` in all ten arms and every read-back lemma of
  `ExpressionProofs.sw` carries it, or (smaller) the users of `Spelled`
  take one more hypothesis, a predicate down the expression's right
  spine (`Binary`'s right, `Negate`'s operand, `If`'s `else` branch)
  saying what follows a block there. E2 then owes that predicate from
  the events: what follows an `if` that ends in a block is the end, a
  line no deeper than the statement, or an enclosing `then` or `else`
  (D4's case again). D3 grows from 20-30 to 30-45, E2 by about 5.

Re-estimate: E2 40-45 left (blocks, lines, notes and blank lines 17;
`if` outside brackets, mutual with lines, 6; `EndsExpression` and the
block ends 7-10; declarations and parameters 8; newest-first against
`Rising` 5), E1 5, D1 75-85 (25-30 with the program change), D2 12-15,
D3 30-45, D4 8-12, glue 8-13: **180-220 lemmas** (130-165 with the
program change), 3 lanes at the measured pace, 4-5 planned. Next: the
shape of statement change 1 (which of the two ways), then D3 and D4
with it, since the rest of E2's induction is stated against the
changed `Spelled`.

## After lane 2 (part 16): D3, D4 and statement change 1 are proved

`stitchwort check` in `sketch/` now says "4 goals open": E1, D1, D2 and
E2. `runsBodyNested` is a theorem of `Toy.Syntax.Proofs`
(`BlockProofs.sw`), and `Spelled` is true of an `if` with a block
branch. `runsIfBlockExample` is an instance: `if a then`, a block `b`,
and `else c` with the `else` starting a line at the block's column,
read back by `runsExpression`.

| Goal | Estimated | Proved | Theorems |
|---|---|---|---|
| D4 | 8-12 | 15 | no expression starts with a keyword other than `if`, whatever reads the nested expressions (`atomDeclines`, `postfixDeclines`, `negationsDecline`, `operatorsDecline`, `chainRuleStops`, `expressionRuleDeclines`, `fuelDeclines`, `expressionDeclines`, two helpers); `statement` declines at `then` or `else` (`bareDeclines`, `closerLineDeclines`, `statementLineDeclines`, `statementDeclinesCloser`, `statementDeclinesEnd`); `SpelledLines` ends with `BlockEnds` |
| D3 with statement change 1 | 30-45 | 8 new, 6 restated, 1 removed | `runsBodyNested`, `runsExpressionFuel`, `afterBrackets`, `afterCloser`, `notAtBack`, `settledBack`, `inlineSpelledBody`, `runsIfBlockExample`; `linesRun`, `runsBodySpelled`, `runsBody`, `runsIfSpelled`, `runsExpressionRule`, `runsExpression` restated |
| E2, the block ends | part of 7-10 | 5 | `afterDeeper` (what may follow a statement may follow the last line of a block inside it, and ends the block), `endsUnallowed`, `operatorOfUnallowed`, `lowLine`, `closerReserved` |

The statement change, as made:

- **An `if` stands only as a whole expression** (`Shaped` asks
  `isChain` of an operator's sides and `isOperand` of what `-`
  negates), so the right spine of lane 1's finding is the `else` branch
  and nothing else. `Spelled` keeps its three arguments. Its arm for
  `If` asks, of each branch, `∀ rest => After layout branchTokens rest →
  SpelledBody layout branch branchTokens rest`.
- **`After layout tokens rest`** is what `ReadsNested`,
  `runsExpression`, `SpelledBody` and `SpelledLines` take where they
  took `EndsExpression layout rest`: `EndsExpression`, and `Settled`:
  outside brackets, what comes next is nothing, `then` or `else`, or a
  token that starts a line no deeper than the statement and is at none
  of the expression's own offsets (`NotAt`; a statement's first token is
  known by its offset, so without this a block's last line can't be
  shown to end).
- **`SpelledBody`'s one-expression case goes by the lines' shape**
  (`SpelledOne`), not "some `bodyOf value`", so that `Spelled`,
  `SpelledBody`, `SpelledOne` and `SpelledLines` are mutual and
  structural. They are in two files of one namespace; nothing moved.
- **`runsExpression` is its own induction on the fuel**
  (`runsExpressionFuel`), not std's `Parse.runsRecursiveWith`, which
  tells the step nothing of the nested parser but what it reads. D4
  needs it to decline at a keyword (`DeclinesNested`), which holds of
  every level but the innermost.

New obligations. Outside the sketch's goals: none; D2's and E2's
statements read as before (`SpelledFile` goes through `SpelledBody`),
and lane 1's `exprSpells` needed two lines (`inlineSpelledBody`). Inside
E2: `Settled` at the end of each statement and body (the next line's
first token is no deeper and at another offset; needs the offsets'
order, which `spellsFile` has as `Descending`), about 4-6 lemmas, in
place of the 2-5 left of "`EndsExpression` and the block ends".

Not done: `if` outside brackets in E2. It is mutual with blocks and
lines (the branch of an `if` is a `SpelledBody`, a block's line is a
`Spelled`), so it is the same induction as E2's blocks, not a part
that comes before it.

Re-estimate: E2 40-45 left (blocks, lines, notes and blank lines 17;
`if` outside brackets, in that induction, 6; `Settled` and
`EndsExpression` at each end 4-6; declarations and parameters 8;
newest-first against `Rising` 5), E1 5, D1 75-85 (25-30 with the
program change), D2 12-15, glue 8-13: **140-165 lemmas** (90-110 with
the program change), 2 lanes at the measured pace, 3-4 planned.

## After lane 3 (part 17): D1, E1 and D2 are proved

`stitchwort check` in `sketch/` now says "1 goal open": E2
(`spellsFile`). `parseHeaded`, `placedOffsets` and `runsFileSpelled` are
theorems of `src/` (in `Toy`'s audit: 1210 theorems, 0 failed), and the
sketch uses them as it used its own open statements; no statement of
the three changed.

| Goal | Estimated | Proved | Theorems |
|---|---|---|---|
| D1 with the program change | 25-30 | 65 | the walk, `Fmt/HeadProofs.sw` (50: `parseHeaded`, `givesHeadedExpression`, one `givesHeaded…` per parser function, `headedBare`, `headedCleared`, `clearedFirstAbove`, the list lemmas); clearing changes nothing where nothing is, and keeps `Shaped` and `Lexical` (15: `noAboveCleared`, `spelledFirstAbove`, `startAbove`, `spelledHeaded`, `shapedCleared`, `shapedHeaded`, four `cleared…`, `ownOffset`, `lexicalCleared`, `lexicalHeaded`, `fineCleared`, `headedOfNoAbove`) |
| E1 | 5 | 8 | `placedOffsets`, `placedBelow`, `pieceOffsets`, `wordOffsets`, `withTrailingOffsets`, `wordLength`, `belowDescending`, `belowWider` (`Fmt/PlaceProofs.sw`) |
| D2 | 12-15 | 6 | `runsFileSpelled`, `declarationsRun`, `groupValues`, `fileOfNotes`, `firstBlankOfAppend`, `groupSomeOf` (`Syntax/FileProofs.sw`, with `SpelledFile` and `SpelledDeclarations` moved from the sketch) |

D1 is over its count and under its time: 45 of the 50 are
`ShapeProofs.sw`'s lemmas again with `HeadedExpr` for `Shaped`, written
in one pass. The estimate counted the new ideas (about 20), not the
walk's one lemma per parser function. D2 is under because
`runsValueSpelled` and `runsFunctionSpelled` already did each
declaration.

The program change, as made:

- **`bareStatement` gives `Bare (layout.headed value)`**:
  `Layout.headed` is the identity inside brackets and
  `Expr.withoutFirstAbove` (down the left spine: a call's callee, a
  field's target, an operator's left side) outside. So "the first token
  of a statement that is an expression, or of a body's one expression,
  holds no comments above it" is a fact about the tree `bareStatement`
  built, with no account of which token was read first. The 103 tests
  (goldens, probes, the disturber, messages) pass unchanged, run without
  the cache.
- **The `let` and `fn` lines are not changed.** Their keyword's comments
  are `layout.comments first` at the layout whose start is `first`'s own
  offset, and `Layout.comments` gives none above there by computation
  (`startAbove`, one line). Clearing them would have been a second
  program change for nothing.
- `Expr.firstAbove` moved from `Fmt/EventProofs.sw` to `Parser.sw`,
  beside `withoutFirstAbove`.

New obligations. Outside the sketch's goals: none. Inside E2, one, and
it is met already: `SpelledOne` and `SpelledInline` (a body that is one
expression) each ask one more fact, `layout.headed value = value`
(clearing changes nothing), which the read-back needs because the
parser now clears. E2 gives it from `HeadedStatement`, which it has as
a hypothesis (`headedOfNoAbove`; `inlineSpells` and `bodySpells` are
updated). A statement's own expression needs no such clause:
its first token is the statement's start, so `spelledHeaded` proves it
from the spelling (`linesRun`). E2's remaining parts will meet the
clause wherever they build a `SpelledOne`: one line each, from the
`headed` hypothesis.

Re-estimate: **E2 40-45 lemmas left** (unchanged: blocks, lines, notes
and blank lines 17; `if` outside brackets, in that induction, 6;
`Settled` and `EndsExpression` at each end 4-6; declarations and
parameters 8; newest-first against `Rising` 5), glue 8-13: **50-60
lemmas**, 1 lane at the measured pace, 2 planned (E2's block induction
is the part no lane has attempted).

## After lane 4 (part 18): E2 and the glue are proved; nothing is open

`spellsFile` is a theorem of `src/` (`Fmt/BlockSpellProofs.sw`), and
`formatDirect` with its theorems is in `Toy.Fmt` (`Format.sw`,
`Fmt/DirectProofs.sw`). The driver calls `formatDirect`: no re-parse, no
check of any kind at run time. `Toy`'s audit: 1272 theorems, 0 failed.
The sketch project is removed (its two parser probes are tests in
`Syntax/Tests/Layout.sw`); this file is its history.

| Goal | Estimated | Proved | Theorems |
|---|---|---|---|
| E2: blocks, lines, notes and blank lines | 17 | 21 | `linesOut`, `notesOf` with `notesOfReverse`, `blankNotes`, `noteNotes`, `notedOf`, `notedLine`, `unspacedFront`, `firstBlankSame`, `SeenTo` with `seenToThen`, `seenBlank`, `seenNote`, `blankSeen`, and what is known of the lines left (`closingNote`, `closingCoded`, `closingBody`, `closedSome`, `opensStarts`, `opensSome`, `opensNote`, `laterOfLines`) |
| E2: `if` outside brackets, bodies | 6 | 9 | `exprOut`, `bodyOut`, `plainOut`, `chainNoIf`, `postfixChain`, `operandChain`, `apartComments`, `keywordComments`, `falseFirst` |
| E2: `Settled` and `EndsExpression` at each end | 4-6 | 12 | `lineAfter`, `lastAfter`, `settledAfter`, `settledDeeper`, `afterBack`, `lowUnallowed`, `startNotLet`, `startColumn`, `startsLow`, `startsAtLine`, `startsDeeper`, `laterApart` |
| E2: declarations and parameters | 8 | 7 | `declarationsOut`, `parametersOut`, `parameterListOut`, `laterOfDeclarations`, `notedDeclarationOf`, `notedDeclarationLine`, `firstBlankOfSame` |
| E2: newest-first against source order | 5 | 7 | `descendingRising`, `descendingOnto`, `risingCons`, `risingFront`, `risingBack`, `risingBelow`, `belowNotAt` |
| E2, all | 40-45 | 56 | and `spellsFile` itself |
| Glue | 8-13 | 6 moved, 6 restated | `parsedPrintPlaced`, `printParses`, `formatDirectAnswers`, `formatDirectRoundTrip`, `formatDirectIdempotent`, `formatAgrees` moved as they were; the file loop's six (`formatFileUnchanged` to `formatFileSettles`) restated for `formatDirect` |

How it went together:

- **One induction, three theorems.** `exprOut` (an expression outside
  brackets: an `if` here, everything else by `exprSpells`, since an
  expression of the parser's shape that isn't an `if` holds none,
  `chainNoIf`), `bodyOut` (one expression on the keyword's line, or a
  block) and `linesOut` (a block's lines) call each other down the tree.
- **The tokens' offsets rise** (`Rising`) all the way down, in place of
  `Leads` alone: a block's line is known from the next by its first
  token's offset, so `NotAt` and `Apart` both come from the order.
- **What follows a statement** is the next line of its block, whose
  first view starts a line at the block's column, or what settles the
  block (`lineAfter`); and what settles a statement settles a block
  inside it and ends that block (`settledDeeper`, lane 2's `afterDeeper`
  without the first token).
- **Comment lines and blank lines** wait as trivia (`SeenTo`), and
  `notesOf` reads them as `spacedNotes` does, the newest first, so each
  step of the induction is one `noteStep`.

New obligations: none outside E2. Inside, one change to lane 1's
statement: `Spells` also says what is above the first view (`first.above
= (waiting pending expr.firstAbove).reverse`), which a statement's notes
need; seven arms of `exprSpells` gained an `rfl`.

Left for Matt: whether the checked `format` stays (the tests call it,
as an oracle beside the proof) or goes.

## Lanes

Measured: 1,048 theorems in 13 parts, 80 a part; parts 12 and 13 were
89 and 40 in 25-27 minutes. 200-250 lemmas is 3 lanes at that pace.

The estimate of lanes left stayed at 2-3 for ten parts, so each lane
found about a lane of new work. I would plan **5-6 lanes** (3 nominal,
times 1.75), 3-4 with the program change. The reason for less padding
than history suggests: the chain now checks end to end, so a new
obligation can only appear inside one of five statements, not between
layers. The reason for any padding: E2 has never been attempted, it is
where all the layers meet, and both new findings of this part (fact d,
the keyword after a block) are in what it needs.

The size is bounded. I see no structural problem with the approach:
the pieces compose as stated, and the two statements that are too
narrow widen without touching anything above them.

## Recommendation

**Finish the full toy; don't cut a fragment as a milestone.** A
fragment (no comments, or no `if` blocks) would re-prove the same
induction twice: comments and blocks are in every predicate already
(`TokenAt`, `SpelledLines`). The order does the fragment's job:

1. E2 first, for expressions and inline bodies, assuming D1, D3 and D4
   as the sketch does: this is where surprises come from, so find them
   before sizing the rest again. Then E2's blocks, lines and
   declarations, and E1.
2. D1 beside it (it touches `Syntax/`, E2 touches `Fmt/`).
3. D3 and D4, D2, the glue.

**One program change removes most of D1** (a decision for Matt; it
extends part 13's finding 2(i)). The parser drops the comments above a
statement's first token by comparing offsets deep inside the expression
parser, so facts (a) and (b) need "the tree's leftmost token is the
first token read", a walk over the tokens read (60-70 lemmas, the
uncertain part of D1). If `bareStatement` (outside brackets) and the
`let`, `fn` lines clear them on the tree they built instead (a
`withoutFirstAbove` down the left spine), (a) and (b) are a 10-arm
induction. The function should be a no-op on every input (facts a and b say
the comments are already empty there; not proved, so the goldens and
the disturber are the evidence), so trees, goldens and messages are
unchanged, and it checks nothing: it can't fail. Cost: the read-back lemmas in
`BlockProofs.sw` gain "clearing changes nothing when nothing is there"
(about 10). Net 45-55 lemmas fewer and one uncertain goal made routine.

No program change removes E2, D3 or D4: they are the theorem.
