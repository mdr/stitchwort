# The direct proof, top-down: what is left (SW-3418, D3620)

Part 14 of "Proving the printer directly" (`NOTES.md`). Fable, 15 Nov
2026. No theorem of the proof itself was proved in this part: it states
the rest, from the goal down, and checks that the statements fit.

## What is checked

`sketch/src/Sketch.sw` (namespace `Toy.Sketch`) defines `formatDirect`
(parse, print, no check of any kind) and proves, from five open lemmas
and what `src/` has proved:

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
| E2 `spellsFile` | E | tokens whose views are those of a trace of `FileEvents file`, with distinct offsets, spell the file | all of the above as hypotheses; `viewsOf`, `Events`, `eventsFree`, `bodyFree` | 70-90 (below) | uncertain |
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
