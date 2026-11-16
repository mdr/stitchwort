# After the toy proof: what we learned, what to tidy, where next

Fable paper lane, SW-3489, 16 November 2026. No builds or tests were run
for this note. Numbers marked **[measured]** were counted here with `grep`
and three short scripts over `tools/toyfmt/src` and `crates/`, or are
quoted from `tools/toyfmt/NOTES.md` and `SKETCH.md`, where the lanes
measured them. Numbers marked **[estimated]** are mine.

The toy formatter (`tools/toyfmt`, the language Sprig) is proved correct
with no check at run time: `printParses`, `formatRoundTrip` and
`formatIdempotent` (`tools/toyfmt/src/Toy/Fmt/DirectProofs.sw`). Matt
asked three questions. This note answers each, then gives a roadmap and
four decisions.

## In plain words

**What we learned (question 1).** The proof was cheap per lemma (about 80
lemmas a lane, most right first time) and expensive in count, and the
count has three causes we can remove: std's parser-proof library says too
little, so the toy rebuilt parts of it three times; the language makes a
few everyday proof steps awkward (16 of the 87 friction points are one
problem, `match` and `rewrite` changing more or less than you meant); and
positions (columns, line starts, offsets) run through two thirds of the
hard layers, because Sprig, like Stitchwort, reads blocks by indentation.

**What to tidy (question 2).** 1,262 theorems, 27,300 lines of proof for
1,680 lines of program [measured]. About 157 theorems (12%) are no longer
used by the final result, including one whole early layer. Three walks
over the parser (201 theorems) are the same walk with three predicates.
Only 17 theorems are plain std facts; the reusable part is not loose
lemmas but four small *theories* (the engine, "tokens don't merge", rule
triples, "the parser keeps P"). A tidy-up could bring the toy to about
900 theorems [estimated] without changing what it proves.

**Where next (question 3).** The real formatter does three things the toy
doesn't: it changes tokens (drops brackets and commas, merges parameters,
inserts `∀`), it moves comments, and it falls back to "leave as written".
All four formatter bugs the fuzzer found overnight are of two kinds that
one design rules out by proof. That design: **the formatter is small
tree-to-tree passes, each proved to keep the meaning, then a printer that
changes nothing but white space, proved exactly as the toy's was.** I
recommend it as the end state, rehearsed first on the toy ("Toy++"),
while std's proof library is fixed. A proved real formatter is about
3,000 to 6,000 theorems [estimated], 3 to 5 toys; the library work should
take a quarter to a third off that.

## 1. What the toy proof measured

| Layer | Files (`tools/toyfmt/src/Toy/`) | Theorems | Not used by the result |
|---|---|---|---|
| The engine: any way a document may print | `Doc/Proofs.sw`, `Readings.sw`, `Words.sw`, `Columns.sw`, `Joins.sw`, `Places.sw` | 246 | 53 |
| The lexer: printed pieces lex back to the same tokens | `Syntax/LexProofs.sw`, `StandProofs.sw`, `Fmt/LexTextProofs.sw`, `StringProofs.sw`, `TextProofs.sw`, `PieceProofs.sw` | 153 | 8 |
| The rules: what each rule's document prints, and where | `Fmt/LayoutProofs.sw`, `WordProofs.sw`, `JoinProofs.sw`, `RuleJoinProofs.sw`, `LaidProofs.sw`, `EventProofs.sw`, `PlaceProofs.sw`, `TokenEventProofs.sw`, `BracketEventProofs.sw` | 399 | 83 |
| What the parser guarantees of its trees (three walks) | `Syntax/ShapeProofs.sw`, `Fmt/ParsedProofs.sw`, `Fmt/HeadProofs.sw` | 201 | 0 |
| The parser reads back what spells a tree | `Syntax/ParserProofs.sw`, `ItemProofs.sw`, `ExpressionProofs.sw`, `BlockProofs.sw`, `FileProofs.sw` | 135 | 7 |
| Spelling: printed tokens with positions spell the tree | `Fmt/SpellProofs.sw`, `BlockSpellProofs.sw` | 113 | 5 |
| Glue and the file loop | `Fmt/DirectProofs.sw`, `Fmt/Proofs.sw`, `Syntax/Proofs.sw`, `Syntax/Token.sw` | 15 | 1 |
| **All** | 34 proof files, 27,349 lines | **1,262** | **157** |

All [measured]. "Not used" means: not reached, following names, from
`printParses`, the round trip, idempotence or the file loop's theorems. It
is a count by name, so it should be confirmed by deleting and checking
(a verifier job, not this lane's).

Other measurements:

- **Program against proof:** lexer, parser, tree, engine and rules are
  1,679 lines; the proofs are 16 times that.
- **Size of a proof:** median 11 lines, mean 19. Twenty proofs are over
  100 lines; five hold 3,144 lines between them (`exprSpells` 1,010,
  `declarationsOut` 902, `linesOut` 472, `exprLays` 402, `exprOut` 358).
  These are the inductions where all the layers meet.
- **Positions are the cost.** In the three layers that carry columns and
  offsets (read-back, spelling, the rules' events), 301 of 428 theorems
  mention a layout, column, offset or zone in their statement (a word
  match, so rough).
- **Pace** (from NOTES and SKETCH): about 80 theorems a lane, a lane
  ending when its context is full, not on the clock; the last 200 lemmas
  took 4 lanes. Estimates of *lemmas left* stayed at "2 to 3 lanes" for
  ten parts running: each lane found about a lane of new work, until the
  rest was stated top-down with open goals (`SKETCH.md`), after which the
  estimates held (200-250 estimated, about 230 proved).
- **Bugs the proof found:** three in the toy (`- -x` printed as a
  comment; a comma inside a comment; `fits` ignoring a waiting comment),
  and the last was also in the Rust engine (SW-3444).

## 2. Question 1: what to improve, for its own sake and for the next proof

The orchestrator's first pass is right in each item. Below it is checked
against the 87 friction points, ordered by what it would save, with what
I'd add.

### 2.1 Std's parser-proof library (the biggest saving)

**The problem.** `Parse.Reads` (`crates/elab/src/std/Parse/Reads.sw:45`)
says what a parser read and what it returned. Three things it can't say
each cost the toy a copy of the library or of a walk:

| What `Reads` can't say | What the toy built instead | Cost [measured] |
|---|---|---|
| Where the parse is (friction 42) | `Parse.Paced` (`std/Parse/Paced.sw:13`), a lemma per operation beside each `reads…` lemma | 19 theorems, 338 lines |
| Anything about items it only looked at, or a fact true of every token (friction 52) | `Parse.ReadsAmong` (`std/Parse/Among.sw:20`): `Reads`' combinator proofs again with one more hypothesis | 18 theorems, 491 lines |
| That a parser *declines* (fails without reading), for token parsers; std has it for characters only (`RunsChars.sw:109` on) (frictions 77, 80) | 15 lemmas by hand (`ExpressionProofs.sw:2177-2311`), and `Parse.runsRecursiveWith`'s induction copied as `runsExpressionFuel` (`ExpressionProofs.sw:1417`) | about 16 theorems |
| "Every parser function keeps P" as one argument | three walks, one lemma per parser function each: `Gives` (`ShapeProofs.sw:16`), `Fair` (`ParsedProofs.sw:32`), the headed walk (`HeadProofs.sw`); the toy's parser has 65 functions | 201 theorems, 3,800 lines |

`readsThen` also guesses its two parsers wrongly often enough that a
second lemma taking them as arguments exists (frictions 19, 44).

**The change.** One design note (SW-3460, SW-3465 and SW-3478 together;
they are one question), then one lane each:

1. *One `Reads` with a parameter for "what is true of the input left"*,
   kept by taking a start away. Plain `Reads` is the case "nothing";
   `ReadsAmong` is the case "every item is fine". Say in the same
   statement that the offset moved by the length read, so `Paced` goes.
   This changes each primitive's proof and no combinator's (friction 42).
2. *A "keeps P" layer in std*: `Parse.Gives parser holds`, with its dozen
   combinator lemmas (`givesDone`, `givesThen`, `givesWeaken`,
   `givesOptional`, …: `ShapeProofs.sw:19-96`, already free of anything
   Sprig), and a lemma to join two walks (`Gives p P → Gives p Q → Gives p
   (P ∧ Q)`). With 1., `Fair` is the same thing.
3. *A declines toolkit for token parsers*: `Declines` through `bind`,
   `optional`, `many`, `operators` and `recursiveWith`, and a
   `runsRecursiveWith` whose step may assume a fact about the nested
   parser.
4. *`readsThen` that takes its parsers from the term, not the goal.*

**The effect.** In the toy: `Paced.sw` and `Among.sw` go (37 theorems),
and the three walks become one walk and two small ones (201 to about 110
[estimated]). In the real formatter the walk is one lemma per parser
function per predicate; its parser has 234 functions (self-hosted-fmt.md
§1), so three separate walks would be about 700 theorems and one joint
walk about 250 [estimated]. This is the largest single saving on the
table, and it is worth having with no formatter at all: any parser in
`aoc/` proved to return well-formed values uses it.

### 2.2 Four theories to keep, not 1,262 lemmas to move

Only 17 theorems of the toy mention nothing but std types (list in §3.2).
What is reusable is four small theories, each already almost free of
Sprig:

| Theory | Where | What it says | Reuse |
|---|---|---|---|
| The engine's readings | `Doc/Readings.sw:28-51`, `Doc/Words.sw`, `Doc/Places.sw:135` (`Lays`), `Doc/Joins.sw:84` (`Joins`); they import only `Toy.Doc` and `Std` | Whatever the width, `print` is one way of reading the document; every word lands where the document lays it | The real formatter's engine is the same engine (the toy's is a port of `crates/fmt/src/printer/engine.rs`). If `Doc` and `print` move to std as a pretty-printing library, 193 live theorems move with them and are never proved again |
| Tokens don't merge | `Joins` is already generic in `follows: Text → Text → Prop` (`Doc/Joins.sw:84`); the lexer's side is `Stands` (`Syntax/StandProofs.sw:27`) | If each printed piece may follow the one before, lexing the text gives the pieces back | The shape carries to any lexer; the per-lexeme lemmas don't. Worth a std statement: "a lexer built with `Parse.locatedToEnd` whose lexemes satisfy *stands* re-lexes a joined text" |
| Rule triples | `Rule` (`Fmt/LaidProofs.sw:366`): before, what is printed, after | A rule's lemma is the rule's document read left to right; 46 rule lemmas checked with three errors (friction 41) | Moves with the engine |
| The parser keeps P | §2.1 | | std |

**The change.** Move `Toy.Doc` (document, printer, 392 lines) and its
theory to std as `Std.Doc` once Toy++ (§4) has shown what the real engine
needs beyond it (`Verbatim` for text blocks, shared documents).
**The effect.** A proved pretty-printing library is useful to anything
that prints (error messages, the dump functions, AoC output), and the
real formatter starts with its engine layer done: 246 theorems it doesn't
pay for [measured for the toy; the real engine is 636 lines of Rust
against the toy's 392, so some more will be needed].

### 2.3 The language and the tactics

Grouping the 87 friction points (stages A-D and parts 1-18):

| Group | Points | Problem | Change | Effect |
|---|---|---|---|---|
| `match` and `rewrite` change more or less than meant | 16 (9, 10, 15, 16, 24, 25, 33, 34, 45, 48, 51, 54, 55, 56, 64, 74) | A `match` rewrites every hypothesis that mentions the scrutinee (26 type errors in one proof, friction 48); `rewrite` can't find a term the goal has already computed past; a second scrutinee whose type mentions the first is refused | (i) `match` says which hypotheses it refines, or leaves named ones alone; (ii) `rewrite` matches up to computation, or its error shows the computed goal; (iii) scrutinees that depend on each other. Until then, the proving guide should lead with what worked first time: equations chained with `Eq.trans`/`Eq.cong` over named terms (friction 68) and taking lists apart by continuation (friction 72) | The largest single source of lost rounds. One design note; partly SW-3441 |
| Names clash | 8 (B3, B4, 32, 38, 58, 59, 75, 85) | A constructor clashes with another type's constructor, with a `def`, or with a type, even where the expected type is known; the error is at every use and never at the new definition | Pick the constructor by the expected type in patterns (SW-510); report "defined twice" at the second definition | Names stop being chosen to dodge the checker (`Chunk`, `Plain`, `Pending`); the real formatter has 94 node kinds and as many token kinds |
| Effects and equations | 5 (8, 13, 14, 20, 21) | No equations for a definition that performs abilities; `bind (bind p f) k` isn't `bind p (x => k (f x))` by computation, so how a parser is *written* decides whether it can be proved | SW-3443 (equations for effectful definitions); bind associativity by computation or as a rewrite `readsThen` applies itself | Programs stop being reshaped for their proofs (eight helper `def`s in part 2 alone) |
| `match` inside a lambda or after an effect | 5 (7, 44, 54, 73, 74) | `E-MATCH-MOTIVE`: each needs a helper `def` | Lift the `match` automatically | Fewer one-use helpers |
| `True`/`False` as propositions | 4 (26, 30, 47, 57) | `True` is proved by `rfl`, not `Trivial`; an impossible case is `Void.exfalso (Bool.falseNotTrue never)` | `Trivial` and `absurd` accept the Boolean readings | Small, constant; a duplicate lemma exists for it (`falseFirst`, `BlockSpellProofs.sw:541`) |
| `cases` | 3 (23, 37, 43) | Splits the goal, never a hypothesis; runs out of budget on ten character comparisons | `cases h`; a decision procedure for "this character is one of these" | The lexer layer (153 theorems) is mostly this |
| Inference | 6 (B6, 19, 40, 44, 60, 82; part 1's 6) | A hole fails far from its cause | Covered by 2.1 item 4 for parsers; the rest are one ticket each | |
| Long conjunctions | 3 (11, 27, 86) | `Spelled`'s arms are five `∃` and `∧` deep; `declarationsOut` matches a 40-deep `Both` chain, `declarationsRun` a 28-deep pattern | Propositions as records with named fields, taken apart by name | The five largest proofs (3,144 lines) are mostly this plumbing |
| Diagnostics | 7 (part 1's 1, 39, 66, 76, 81, 85, 86) | One unbalanced bracket gave 2,242 warnings and errors in five other files, after SW-3439's fix (frictions 76, 81) | No warnings from a file with a parse error; a bracket-balance hint per `match` arm | Every error in the last two lanes was a bracket or a name clash (friction 86) |
| Termination | 5 (B2, A2, 62, 63, 78) | Recursion through `List.map` over a field needs a helper per list; mutual parsers need fuel by hand | Nested recursion through `map`; already noted for the 94 kinds | Fewer helpers in the tree's rules; partly removes the list lemmas below |
| Character patterns | 2 (31, 50) | A function with character-literal patterns doesn't compute on an unknown character; its equation lemmas work but are found by trial | Document `f.eqN`; show them in `stitchwort goal` | |
| Tools | 6 (12, 18, 29, 53, 70, 84) | A std lemma costs a lane about 4 minutes of tests for three theorems (friction 70); the audit warns "no input made the hypotheses true" for every parser-state hypothesis (SW-3449); **`stitchwort test` answered "103 from the cache" after `bareStatement`, which the tests reach, had changed (friction 84; the lane wasn't sure whether the cache was stale or right)** | A light path for a std lemma that adds no definition; and friction 84 deserves a ticket of its own now: if the cache was stale, it is the one item here that could hide a real failure | |

What went well deserves equal weight, because it says what not to
change: continuation-style predicates through four mutual definitions
(friction 35), unreachable arms left out (65), a new constructor found by
`E-NONEXHAUSTIVE` through four proof files in three runs (67), a 1,400
line mutual induction with no type error (86), and mutual predicates
across two files (78).

### 2.4 How to run a large proof (process)

**The problem.** For ten lanes the amount left did not shrink.
**The change.** State the whole chain top-down first, with every missing
lemma an open goal in a side project, and check that the statements fit
(`SKETCH.md`, D3620). **The effect.** After that, estimates held to
within about 15% and four lanes finished it. For any future proof of
this size: sketch first, then lanes. Also from the toy: test each
finished layer against a deliberately broken program (each part did), and
change the program when a small change deletes a large proof (clearing
comments on the tree, `Parser.sw:347`, removed 45-55 lemmas of D1's
walk).

## 3. Question 2: refining the proof we have

### 3.1 Delete what the result doesn't use (about 157 theorems)

By layer [measured, by name]:

- `Fmt/LayoutProofs.sw`, all 56: the first attempt at "which breaks land
  at a statement's column" (`Keeps`, `statementScan`), replaced by
  `Events`. Nothing outside the file mentions it.
- `Doc/Columns.sw`, 21 of 23 (the `Measured` invariant), and
  `Doc/Proofs.sw`, 27 of 42 (the budget proofs ending in
  `printBudgetEnough`, and the five "after a comment" lemmas). The budget
  proof is how engine bug 3 was found, and says something of its own
  (the printer never stops for lack of budget), so keep it if wanted as
  an engine fact; the final theorem doesn't go through it.
- `Fmt/LaidProofs.sw`, 13 (`softRule`, `hardRule`, `hardUnder`, as part
  13 already noted, and ten more), `Fmt/PlaceProofs.sw`, 9 (the eight
  `…Placed` lemmas at 297-385).
- 10 are examples (instances kept on purpose) and should stay.

**Effect:** about 145 theorems and 2,000 lines go, with no change to
what is proved. A Sonnet lane; the verifier's audit is the check.

### 3.2 Generic facts for std (few)

The 17 theorems that mention only std types, with where they'd go:

| Theorem | Where | Std home |
|---|---|---|
| `textOfChars`: `Text.fromList piece.toList = piece` | `Fmt/PlaceProofs.sw:248` | `Text` |
| `indentLength`: `(" ".repeat n).length = n` | `Doc/Columns.sw:38` | `Text.repeat` (generalise to any one-character text) |
| `indentSpaces`, `spacesAppend`: all-spaces through `repeat` and `++` | `Doc/Words.sw:33`, `Fmt/PieceProofs.sw:71` | `List.all` through `++` and `replicate`, for any test |
| `takenAll`: `rest.takeWhile passes` all pass | `Fmt/LexTextProofs.sw:454` | `List.takeWhile` |
| `commentTaken` | `Fmt/LexTextProofs.sw:459` | generalise: `takeWhile` of a list whose first items pass |
| `lastOfCons`: a non-empty list has a last | `Fmt/WordProofs.sw:393` | `List.last` |
| `wordLength`, `gapNoBreak` | `Fmt/PlaceProofs.sw:502`, `Doc/Places.sw:430` | `Text.all` facts |
| `notAmong` | `Syntax/LexProofs.sw:63` | goes with a `cases` that decides character membership (§2.3) |
| `sameOffset` and `ownOffset` (the same statement twice), `succNotZero`, `consNotNil`, `falseFirst`, `lowUnallowed` | `Fmt/SpellProofs.sw:1821`, `Syntax/ExpressionProofs.sw:1696`, `Fmt/RuleJoinProofs.sw:323`, `Doc/Places.sw:583`, `Fmt/BlockSpellProofs.sw:541`, `:262` | already in std under other names, or one `omega`/`cases`; delete |
| `escapeSegmentPaced` | `Fmt/LexTextProofs.sw:34` | goes when `Paced` does |

Beyond these, two families are generic in all but name:

- **Lists of numbers in order.** `Descending` (`Fmt/PlaceProofs.sw:476`)
  and `Rising` (`Fmt/SpellProofs.sw:1859`) with their lemmas
  (`risingCons`, `descendingRising`, `belowDescending`, about 12): a std
  `List.Sorted` with "reverse of descending is rising" and "sorted
  strictly means no two equal" replaces them.
- **"P of every item" through list operations.** 62 theorems are named
  `…Append`, `…Reverse`, `…Concat`, `…WithoutFirstBlank` or `each…`
  [measured], one set per predicate per list type (`shapedItemsAppend`,
  `lexicalItemsAppend`, `headedItemsAppend`, …). Where the predicate is
  `List.All P`, std has these already; the toy defines each list
  predicate by recursion instead (friction B2's helper-per-list rule
  pushes that way). Restating them over `List.All` removes perhaps 40
  [estimated].

### 3.3 Near-duplicate families

- **The three walks** (§2.1): `ShapeProofs.sw` (77), `ParsedProofs.sw`
  (74), `HeadProofs.sw` (50). The lemma names line up one to one
  (`givesAtom`/`fairAtom`/`givesHeadedAtom`, and so on for 45 parser
  functions); lane 3 wrote 45 of `HeadProofs.sw`'s 50 as clones in one
  pass. Even before any std work, one walk proving the conjunction
  (`Shaped ∧ Lexical ∧ Headed`) over `ReadsAmong` would do: 201 to about
  110 [estimated].
- **Per-lexeme and per-token-kind sets**: the ten `…Event` lemmas
  (`SpellProofs.sw`) and eight `…Placed` (`PlaceProofs.sw:297-385`, now
  unused) are one statement per token kind. A statement over "a token of
  kind k with text t" with the kind as a parameter would make each one.
- **Engine invariants**: `Uniform`, `Measured`, `Joins`, `Lays` are four
  invariants carried down the same work list with the same 26-arm
  `match` (NOTES, "What made it cheap"). A single "every step keeps I"
  lemma taking the invariant's per-operation facts would save little now
  (two of the four are being deleted) but should be how `Std.Doc` states
  it.

### 3.4 Could the structure itself be simpler?

Three ideas, in order of confidence.

**(a) One fewer statement by moving a fact into the program (sure).**
Done once already: the parser clears comments above a statement's first
token on the tree it built (`Expr.withoutFirstAbove`, `Parser.sw:347`),
and D1 fell from 75-85 lemmas to a 10-arm induction plus a clone walk.
The same move applies to `Shaped` and `Lexical`: have the parser build
values that can't be ill-formed (a `Name` that carries "not a keyword",
an operand type that can't hold an `if`), so the predicate is true by
type and its walk disappears. This is the standard correct-by-
construction trade: the proofs move into the parser's own code as small
obligations where each value is built. **Effect:** up to all three walks
(201 theorems) become typing [estimated; not tried, and how pleasant
Stitchwort makes values-with-proofs in a tree of mutual types is itself
the experiment]. Worth one Toy++ lane to try on `Name` and the operator
levels.

**(b) Make the rules' output carry the tokens (likely).** Today a rule
builds a document of text chunks, and three layers recover from the
printed text which tokens those were and where: words (`Writes`,
`WordProofs.sw:22`), events (`Events`, `EventProofs.sw:44`), views
(`viewsOf`, `TokenEventProofs.sw:74`), then `Seen` (`SpellProofs.sw:209`)
to get back to tokens. If a document's leaf *is* a token with its
comments, "the document's tokens are the tree's tokens" is a fold proved
once per rule by `rfl`-like steps, and the engine's theorem hands back
tokens with places directly. The events and views layers (about 150 of
the 399 rule theorems [estimated]) shrink to the engine's statement.
This is close to Danielsson's correct-by-construction pretty-printing,
where the document's type is indexed by the grammar and the value, so
only documents that parse back to that value can be built at all (his
abstract claims exactly print-then-parse for an unambiguous grammar; I
have not checked whether it stretches to an indentation-sensitive
grammar or to comments, and I'd assume not without work).

**(c) Take the layout rule out of the parser (uncertain, largest).**
301 of 428 theorems in the hard layers mention positions [measured,
§1]. They do because the toy's parser checks columns as it goes
(`Layout` is a parameter of every parser function), so every read-back
lemma carries a layout, and the proof needs `Settled`, `After`, `NotAt`,
`BlockEnds`, `Rising` (`ExpressionProofs.sw:463-475`,
`BlockProofs.sw:507`) to say where a block ends. The alternative is a
pass between lexer and parser that turns columns into explicit
block-open, block-close and line tokens; the parser is then an ordinary
grammar over tokens and its read-back has no positions in it; and one
theorem says the printer's line starts produce those tokens. **Effect:**
positions would be confined to one layer [estimated: the read-back and
spelling layers, 248 theorems, lose perhaps a third]. **Risk:** the real
Stitchwort parser checks columns inside the parser too
(`crates/syntax/src/parser.rs:12-20`), and its rule "brackets continue
lines however far left" may not be a clean pre-pass. So: an experiment
on the toy, not a recommendation yet.

A different spec of the *style* would not shrink much: the layers that
depend on style (rule triples, `Events`) were the cheap ones, as part 1
predicted.

**A fair target for the tidy-up:** 1,262 → about 1,100 by deletion
(3.1), → about 1,000 by one walk (3.3), → about 900 with `List.All` and
`Sorted` (3.2) [estimated]. Ideas (a) to (c) are experiments for Toy++,
not tidy-up.

## 4. Question 3: the real formatter

### 4.1 What it does that the toy doesn't [source: `crates/fmt/src`]

| Beyond white space | Where | Kind |
|---|---|---|
| `∀` inserted after a theorem's name | `printer/mod.rs:10` | adds a token |
| Redundant brackets dropped, if the text without them parses the same | `printer/parens.rs:1-12` | removes tokens, on the text, checked by re-parsing |
| Neighbouring parameters of one type merged, `(a: Nat) (b: Nat)` to `(a b: Nat)` | `printer/merge.rs:1-11` | rewrites tokens, on the text, checked on its own |
| A comma before a closing bracket dropped; a comma that starts a line moves to the end of the line above, its comments becoming the next item's | `printer/rules.rs:334-369`, `:1081` | removes or moves tokens, inside the printing rules |
| A comment written before closing brackets or commas is printed after them | `printer/rules.rs:455-458` | moves a comment to another token, inside the rules |
| A `"""` text block's lines move with their line | `printer/rules.rs:312`, `check.rs:37` | changes a token's text, not its value |
| A declaration whose output fails a check, or a node with no rule, is left as written | `printer/mod.rs:12-14`, `rules.rs:475` | fallback |

`check.rs:24-32` shows the price: the "same tokens" check ignores every
comma and every round bracket, and leans on the tree check to catch a
wrong one.

Its layout rules are also richer than Sprig's (match arms at a column,
lines that start with an operator, bracket continuation, `then`/`else` at
a block's column, hugging the last argument): 73 rule functions in 1,908
lines against the toy's 33 in 269 [measured].

### 4.2 What the overnight fuzz bugs say

All four are "formatting twice gives a different answer", and they are of
two kinds:

- **A rewrite that isn't finished in one pass.** SW-3482: doubled
  brackets lost one pair per run.
- **The layout depended on something the printed text doesn't keep.**
  SW-3481, SW-3485, SW-3487: a comment written before a closing bracket
  is printed after it, so the second run sees the comment on a different
  token and lays the code out differently. Each was fixed by one more
  place asking `comment_ends_at_closers`.

In the toy neither can happen, and not by testing: `print` takes only
the tree, and `parse (print tree) = tree`, so the second run prints the
same tree. The real formatter breaks that equation on purpose (the
output's tree is *not* the input's: brackets, commas and comments have
moved), and it does so in three different places: on the text before
parsing, inside the rules, and inside the engine's comment handling.
That is the thing to fix in the design, whatever is proved.

### 4.3 The directions

**A. Validate, don't prove (the current plan's theorems).** The
self-hosted formatter as planned (self-hosted-fmt.md §7, with D3617):
re-read the output, answer only if the tree comes back.
*Carries over:* stage D of the toy (15 minutes [measured]).
*End state:* the theorems are true but say "if it answers, the answer is
right"; the check runs on every changed declaration for ever; the
fallback stays; bugs like last night's are still found by the fuzzer,
one at a time. It is the floor, not Matt's stated goal (prove it, drop
the check).

**B. Port the Rust formatter as it is, prove it afterwards.**
Self-hosted-fmt.md's stages 0-6 (function by function, byte for byte),
then a direct proof.
*New:* everything in 4.1, in the shape 4.1 shows: rewrites on text,
token changes inside rules.
*Risk:* high. The toy's proof needed the program changed six times
(the `- -x` space, `closeAfter`, `fitsHere`, `symbolsKind`, `itemsFrom`'s
fuel arm, clearing first comments); a program ported to be byte-identical can't
be changed without changing the Rust one too. And the proof would have
to describe "the same tree up to commas, brackets and moved comments"
inside every layer.
*Size:* the largest of the four; I would not estimate it.

**C. Passes, then a printer that only chooses white space
(recommended end state).**

```
parse  →  tidy₁ → tidy₂ → … → tidyₙ  →  print
          (tree to tree)                (white space only)
```

Each tidy pass is a function on trees: drop redundant brackets, merge
parameters, insert `∀`, drop the comma before a closer, move a comment
that sits before closers to after them, cap blank lines. What is proved:

1. Each pass keeps the meaning: `meaning (pass tree) = meaning tree`,
   where `meaning` forgets exactly what the formatter may change
   (question in §6).
2. Each pass finishes: its output is *tidy* for that pass, and a tidy
   tree is left alone. (SW-3482 is this theorem failing.)
3. Each pass keeps what the earlier ones tidied, and what the parser
   guarantees (`Shaped` and friends).
4. For a tidy tree, `parse (print tree) = tree`, at every width: the
   toy's theorem, with the toy's layers. (SW-3481, 3485 and 3487 are
   this failing.)
5. From 1-4, in a few lines as in `DirectProofs.sw`: the output parses,
   means what the source meant, and formatting it again changes nothing.

*Carries over from the toy:* all of 4 (engine, lexing, rule triples,
events, spelling, read-back, the walks) and the glue. The toy already
has one pass (clearing first comments) and the pattern for 3
(`shapedCleared`, `lexicalCleared`, `headedOfNoAbove`: 15 lemmas).
*New:* the passes and `meaning`; the richer layout rules; text blocks
(a token whose text changes and value doesn't: lexer layer); 94 node
kinds.
*The fallback goes.* "Left as written" exists because a check can fail.
With no check there is nothing to fall back from, and over std, `aoc/`
and `games` no declaration uses it today (0 of 15,829 [measured,
self-hosted-fmt.md §1]). Part 2 of the toy called `AsWritten` "the piece
that doesn't fit"; D3618/D3619 removed it there by giving every comment
a place, and the real rules need the same.
*Risks:* (i) the tree must be typed per construct for the proofs to go
by cases, where the Rust tree is one node type with 94 kinds; (ii) the
rules are still changing weekly, so their layer should be proved last;
(iii) proof checking time at five times the toy's size is unmeasured;
(iv) `meaning` is a definition we trust, not a theorem, until the
lowering is also in Stitchwort.
*The Rust formatter can take the same shape first*, cheaply and with no
proofs: moving its comma and comment handling out of the rules into
passes over the tree would end this family of fuzz bugs there too, and
keep the two formatters comparable byte for byte.

**D. One description for both parser and printer.** Write each construct
once, as a description that runs as a parser one way and a printer the
other (Rendel and Ostermann's invertible syntax descriptions), so
print-then-parse holds by construction.
*End state:* attractive: no read-back layer at all. *Why not now:* their
printer has no layout choice, widths or comments, and Stitchwort's
grammar is indentation-sensitive; a formatter's printer and parser
differ in exactly the parts that make it a formatter. The toy already
has the useful half of the idea: `Spelled` (`ExpressionProofs.sw:363`)
is a grammar written as a relation, the parser is proved against it one
way and the printer the other. A direction for a later language feature
(deriving `Spelled` and its read-back from a grammar), not a plan.

### 4.4 Toy++ (this answers SW-3434)

**The problem.** Direction C has two new proof shapes nobody has tried:
a pass with its three theorems, and a printer proved for tidy trees
only. Trying them first on the real formatter means trying them at 94
node kinds.
**The change.** Add to Sprig only what exercises the new shapes, one of
each kind in 4.1:

1. a pass that removes tokens: redundant brackets, `((x))` and `(x)`
   where an operand already stands, with the Rust rule "a pair that
   touches a comment stays";
2. a pass that merges: `fn f(a, b)` given an optional type per
   parameter, merged when neighbours share one (or simpler: a cosmetic
   keyword inserted, as `∀` is);
3. a pass that moves a comment: one before a closing bracket goes after
   it; and the comma before a closer goes;
4. `meaning`, the three theorems per pass, and `printParses` restated
   for tidy trees;
5. as experiments, kept only if they pay: §3.4 (a) on `Name`, (b)
   token-carrying documents, (c) the layout pass.

Leave out the fallback (it goes) and text blocks (a lexer detail; add
if a lane has room).
**The effect** [estimated]: 200-350 new theorems on a tidied toy, 3 to
5 Fable lanes including a top-down sketch first, a day or two of
elapsed time. It decides: the exact statements of 1-5 above; whether
`meaning` is pleasant to write; how much each of (a), (b), (c) saves.
Each of those changes the real formatter's design, so they are worth
knowing before its parser is written.

### 4.5 Size of the real thing, from the toy's costs

| Layer | Toy [measured] | Scales with | Real, direction C [estimated] |
|---|---|---|---|
| Engine | 246 (193 live) | one engine; 636 lines of Rust against 392 | 300-400, or about 100 new if `Std.Doc` exists |
| Lexer | 153 for 24 functions | lexer size (1,535 lines of Rust; text blocks, interpolation) | 450-900 |
| What the parser guarantees | 201 = 3 walks × 65 functions | parser functions (234) × walks | 700 as three walks, 250 as one, less with §3.4 (a) |
| Read-back | 135 | parser functions, or node kinds (94 against 17) | 500-750 |
| Rules: words, joins, events | 399 (316 live) for 33 rule functions | rule functions (73) to rule lines (7×) | 750-2,400 |
| Spelling | 113 | node kinds | 500-650 |
| Passes and `meaning` | 15 (one pass) | 6 passes | 150-300 |
| **Total** | 1,262 | | **about 3,000-6,000** |

At the toy's pace (80 theorems a lane, lanes of 25-50 minutes) that is
40-75 Fable lanes, 25-60 lane hours, and I'd plan 1.75 times that as
`SKETCH.md` did, for the same reason: until the chain is stated
top-down, each lane finds another. Very low confidence at the top of
the range: the rules layer's spread is a factor of three, and nothing of
the real formatter has been tried. Building the formatter itself is
separate (42-59 lane hours in self-hosted-fmt.md §8; the toy came in at
about a seventh of its estimate).

### 4.6 A consequence for the parser: `Parse`, not hand-written

SW-3414 recommended a hand-written parser for the real formatter: std's
`Parse` is 7-10 times slower, and the safety check pays that twice. A
proved formatter changes both halves of that argument. Every one of the
336 parser theorems (walks and read-back) rests on `Parse.Reads` and
`Parse.Runs`; a hand-written parser over arrays and indices has no proof
library at all. And with no check there is no second parse: the toy
formats at 2.2 s per MB without it against 4.3 with [measured], about
15 s for the repo at the real formatter's scale against a 20 s target
[estimated in SW-3414]. So for direction C the parser should be written
on `Parse`, and making `Parse` faster (operations in place) becomes
formatter work as well as std work.

### 4.7 How the two goals feed each other

Ranked by what each saves the real formatter [estimated], with its value
if no formatter were ever proved:

| Std or language work | Saves the real proof | Value alone |
|---|---|---|
| One `Reads` with an invariant and offsets; `Gives`; joint walks (§2.1) | 450-500 theorems | every proved parser |
| `Std.Doc` with its theory (§2.2) | 200-300 | a proved pretty-printer for everyone |
| `match`/`rewrite` refinement (§2.3) | rounds, not theorems: the main source of retries | every proof |
| Records as propositions; `cases h` (§2.3) | the 3,000 lines of the five largest proofs, times five | every proof |
| Constructor names by expected type (§2.3) | makes 94 kinds and their tokens nameable | everyone |
| Declines toolkit (§2.1) | 50-100 | parsers with alternatives |
| `Parse` speed (§4.6) | makes the proved formatter fast enough | AoC, tools |
| `List.All`, `List.Sorted` facts (§3.2) | 100-200 | small, wide |

The first two are also the first two to do: they are std work with a
known shape, they can run now beside anything else, and the tidy-up of
the toy is their test.

## 5. Roadmap

Each step says what it decides or unlocks. Steps 1-3 can run side by
side.

1. **Tidy the toy** (§3.1-3.3): delete the unused 145, one joint walk,
   `List.All`/`Sorted`. Sonnet, 1-2 lanes. *Unlocks:* a 900-theorem
   toy that is a fair baseline for everything after; std gets its
   handful of lemmas.
2. **The parser-proof library design note** (SW-3460 + SW-3465 +
   SW-3478 as one note, with the declines toolkit), then its lanes.
   Opus. *Decides:* the shape of `Reads` for good. *Unlocks:* the
   real formatter's cheapest 450 theorems; the toy is the regression
   test.
3. **Language tickets from §2.3**, in this order: the stale test cache
   (friction 84), no warnings after a parse error, "defined twice" at
   the definition, constructors by expected type, `cases h`; then one
   design note for `match`/`rewrite` refinement and records as
   propositions. *Unlocks:* cheaper lanes for all proof work.
4. **Toy++** (§4.4), sketch first. Fable for the sketch and the hard
   inductions. *Decides:* the theorem statements of direction C,
   `meaning`, and which of the three structural ideas to keep.
5. **`Std.Doc`** (§2.2): move the engine and its theory to std, shaped
   by what Toy++ needed. *Unlocks:* the real engine layer.
6. **Reshape the Rust formatter into passes and a white-space-only
   printer** (no proofs). *Decides:* whether direction C's shape holds
   for all 94 kinds; ends the comment-moves-the-layout bug family where
   users are today.
7. **Rewrite self-hosted-fmt.md** for direction C (this replaces
   SW-3417's refresh): a typed tree, the parser on `Parse`, passes, no
   fallback, no check; proofs in the order engine, lexer, parser,
   passes, rules last. Then its stages.

Steps 1-5 are each useful if step 7 never happens.

## 6. Decisions for Matt

Four. The orchestrator should number them.

**Q1. Is "passes, then a white-space-only printer" (direction C) the end
state for the Stitchwort formatter?**
*The problem:* the formatter changes tokens in three places (on the text,
in the rules, in the engine), which is where all four of last night's
fuzz bugs came from and what makes it unprovable as it stands.
*The change:* every token change becomes a small tree-to-tree pass with
three theorems; the printer changes white space only and is proved as
the toy's was; "left as written" goes.
*What it should do:* formatting twice is the same by proof, not by
fuzzing; no check at run time; style changes touch only the cheapest
proofs. **[rec: yes]**

**Q2. Do Toy++ next (3-5 Fable lanes), before the real formatter's
stage 0?**
*The problem:* passes and `meaning` have never been proved here, and the
three ideas that could shrink the proof by a third are untested; finding
out at 94 node kinds costs five times as much.
*The change:* add one rewrite of each kind to Sprig and prove it,
sketch first.
*What it should do:* fix the real formatter's theorem statements and
parser design before its parser is written. **[rec: yes; the tidy-up
and the std library note start now either way]**

**Q3. What should "the same program" mean for a formatter that rewrites?**
*The problem:* the Rust formatter compares the compiler's tree, built by
4,000 lines of Rust lowering that a Stitchwort proof can't mention.
*The change:* define `meaning` in Stitchwort: the tree with exactly the
formatter's freedoms forgotten (redundant brackets, parameter grouping,
`∀`, the comma before a closer, which side of a closer a comment sits),
and prove each pass keeps it. Keep the Rust hash check in the fuzzer as
the cross-check that `meaning` forgets nothing the compiler sees.
*What it should do:* a theorem that is honest about its one trusted
definition (about a page), until the lowering is itself in Stitchwort.
**[rec: yes, `meaning` in Stitchwort plus the fuzz cross-check; not a
port of the lowering]**

**Q4. Should the proved formatter's parser be written on std `Parse`,
reversing SW-3414's "hand-written"?**
*The problem:* every parser theorem of the toy rests on `Parse`'s proof
library; a hand-written parser would need its own. SW-3414's speed
argument assumed a second parse for the check, which the proof removes.
*The change:* the real parser on `Parse`; `Parse` speed becomes part of
the formatter's work.
*What it should do:* about 15 s for the repo [estimated from the toy's
2.2 s per MB], inside the 20 s target, with 336 theorems' worth of
library to stand on. It gives up "follows the Rust parser function for
function". **[rec: yes, confirmed by a timing in Toy++ before stage 0]**

Not Matt's, noted for the orchestrator: whether `printBudgetEnough` and
its 27 lemmas stay as an engine fact (my call would be to keep them,
moved to `Std.Doc`'s tests of the engine); the order of the §2.3
tickets.

## Tickets this note absorbs or suggests

- **SW-3434** (Toy++): answered by §4.4; retitle as the Toy++ sketch
  lane if Q2 is yes.
- **SW-3417** (refresh self-hosted-fmt.md): replaced by roadmap step 7,
  which waits for Q1 and Q4.
- **SW-3460, SW-3465, SW-3478**: one design note (§2.1), with the
  declines toolkit and `readsThen`'s inference.
- New: tidy the toy (§3.1-3.3); stale test cache (friction 84); no
  warnings from a file with a parse error (frictions 76, 81); "defined
  twice" at the second definition (frictions 59, 75, 85); `List.Sorted`
  and the `Text`/`List` lemmas of §3.2; `Std.Doc` (after Toy++); the
  Rust formatter's comma and comment handling as passes (after Q1).

## Sources

For the two outside systems named (checked 16 Nov 2026; I read the
abstracts and publication pages, not the full papers):

- N. A. Danielsson, "Correct-by-Construction Pretty-Printing", DTP 2013:
  <https://www.cse.chalmers.se/~nad/publications/danielsson-correct-pretty.html>
- T. Rendel and K. Ostermann, "Invertible Syntax Descriptions: Unifying
  Parsing and Pretty Printing", Haskell Symposium 2010:
  <https://ps.cs.uni-tuebingen.de/publications/rendel10invertible/>

That invertible syntax descriptions have no layout choice or comments is
my reading of the abstract (one program read as a parser or as a
printer), not something the paper's page states.
