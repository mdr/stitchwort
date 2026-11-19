# Slice 1 checkpoint, and the route for its last open goal (SW-4184)

Fable, paper review, 19 Nov 2026, against `main` at 9395074ab. Nothing
was built or checked. That `tools/fmt` checks with one open goal is
taken from SW-4176's report; I confirmed by grep that the only `?` in
`tools/fmt/src` is `Fmt/SettleParseProofs.sw:316`, and that there is no
`axiom` or `trusted`.

How claims are marked: **[source]** read in the code today;
**[measured]** a run of mine today (three runs of the release
formatter, which is the Rust one); **[reported]** from a lane's report
or an earlier review; **[estimated]** my judgement.

## Verdict

**B, the checkpoint: sound with notes.** The three top theorems say
what D3687 asks, and nothing on the path was narrowed or given a
condition today. Slice 1 is not done: `formatAccepts1` rests on the one
open goal, `settledParsesMoved1`. The notes are in section 2; the one
worth acting on is that "keeps the program" is stated about the
driver's own parse (after rule N), so the three theorems don't yet
combine into one sentence about the language's parser without the open
goal's fact.

**A, the route: stop the parser seeing rule N's mark, instead of
proving the mark harmless.** The driver parses the settled leaves with
the lexer's own tokens put back (the same comments, the closer's line
start as the source had it). Then the tokens the parser reads are the
source's for every source, `settledParsesKept1` covers every case, and
`settledParsesMoved1` is deleted, not proved. One Opus lane, about 45
minutes [estimated]. Rule N, its proofs and the printer are untouched.

**This changes the driver's definition, so it is Matt's to agree.** No
change in output or in what is accepted is known or expected: the two
drivers differ only on a source where the mark changes the parse, and
none was found in 14,349 such sources [reported, SW-4131 §4]. I can't
offer a proof that they never differ: that proof is the open goal
itself. If they ever did differ, the new driver would be the one that
reads the source as the language does. The cases are in section 1.4.

## 1. The route for `settledParsesMoved1`

### 1.1 What is open, exactly

`Lexed.settledOnce` (`Syntax/Settle.sw:338`) runs `withBareLastCommas`
and then rule N. For a last comma before a closer, `commaMoved`
(`Settle.sw:297-308`) moves the comma's comments and sets the closer's
`lineStart` to `starts || closer.token.lineStart` (line 305). Rule N
needs that: `stepsBack` (`Settle.sw:124-131`) stops a closer's trailing
comment on a leaf that starts its line when going further would pass
own-line comments or a line ending in a comment. With the comma bare,
the closer has to make that stop itself, or the comment lands on the
comma (SW-4131 §1; this is what removed spike K1's trouble).

The driver then parses those leaves (`Fmt/Driver1.sw:62`). When the
comma starts its line and the closer follows on the same line
(`[1, 2⏎  ,]`), the closer's `lineStart` goes from false to true, so
the tokens differ from the lexer's and `parseKeepsTokens1`
(`Fmt/SettleParseProofs.sw:231`, "same tokens, same parse up to
comments") doesn't apply. That is `settledParsesMoved1`
(`SettleParseProofs.sw:307-316`).

### 1.2 What the parser can see of the mark [source]

`itemsAfter` (`Syntax/Parser.sw:52-69`) turns the one changed bit into
three changed fields:

| Field | Change | Who reads it |
|---|---|---|
| the closer's `lineStart` | false to true | `startsBlock` (638), `blockEnd` (688), `lineHasSemicolon` (712), `blockOffset` (785), `stopsByLine`, and every other reader that tests an item's line start |
| the closer's `glued` | true to false when it touched the comma | lines 555-587, 1525, 1696: all about a `.`, a sign, a numeral, a name, or `()`. None can be a closer after a comma. Harmless |
| `lineIndent` of the closer and of every later item on its line | the comma's column to the closer's | only `headIndentOn` (802), compared only for `match`, `if`/`then`/`else` and `|>` (833, 863, 1157, 1180, 1240). None is in slice 1's alphabet, so harmless **in slice 1**. In the whole language it is a live reader: a `|>` line continues a chain only if it isn't left of this column |

So SW-4183 is right that an item-by-item "alike" relation can't carry
the proof: whether `startsBlock` or `stopsByLine` agree on the marked
closer depends on where the walk is (inside a bracket, after a comma),
not on the two items.

### 1.3 The routes

**Route 1: generalise `Follows` to items alike up to a closer's line
start.** A new list-level relation, and the roughly 70 layout readers
re-proved for it, with context for the closer. 3 to 5 Opus lanes after
a Fable sketch, 3 to 5 hours [estimated; SW-4132's eight lanes took the
morning]. Risks: intermediate lemmas false as first stated, and the
work is per slice: the `lineIndent` column above is harmless only
because slice 1 has no `|>`, `if` or `match`. Slice 2 onwards would
have to prove more, and I can't say the fact is true there. I did not
find a counterexample, and did not search.

**Route 2 as briefed: rule N leaves the closer's line start alone.**
This changes printed output, so I don't recommend it. Without the mark
`stepsBack` walks from the closer onto the bare comma [source]. The
formatter's output today, from the Rust formatter, which the self-hosted
rule mirrors by SW-3964's design [measured; the self-hosted driver was
not run]:

```
def x: T := [1, 2 -- two        def x: T := [
  ,] -- d                         1,
                                  2 -- two
                                ] -- d

def x: T := [1, 2               def x: T := [1, 2
  -- above                        -- above
  ,] -- d                       ] -- d
```

Unmarked, in the first source the walk stops on the comma (it starts
its line and the line before ends with a comment), so `-- d` is put on
the comma, and rule 2 then carries a comma's comment to the token
after it: `-- d` would print on its own line above the `]`. In the
second the comma is bare with no comment before it on the line above,
so the walk goes on to `2`: `-- d` would print after `2`, before
`-- above`, and the two comments swap. That breaks "comments keep
their order", and `homedBehind` fails as in spike K1. [source: read
from `stepsBack`, `trailingAt`, `commaMoved`; not run.]

**Route 2d: rule N reads an "effective" line start** (a closer counts
as starting its line if the bare comma before it does), and
`commaMoved` stops marking. Same output by design, and the driver's
text is unchanged. But rule N's definition changes, and it is shared
with the output side; `bareSettles` and the `barish` invariant
(`SettleBareProofs.sw:126`, "a bare last comma starts a line only if
its closer does") are restated. The three settle proof files mention
`lineStart` 83 times. Opus, 60 to 90 minutes, low confidence
[estimated]. No gain over the next route.

**Route 3, recommended: the parser reads the lexer's tokens.** Add,
beside `settledOnce`:

```
--| The settled leaves as the parser reads them: each with the lexer's
--| own token, so the parse depends on rule N only through comments.
def Lexed.settledSource (lexed: Lexed): Lexed :=
  let once := lexed.settledOnce
  { once | leaves = List.zipWith (leaf raw => { leaf | token = raw.token }) once.leaves lexed.leaves }
```

(The name and the exact form are the lane's; restoring only `lineStart`
does the same.) The driver and `parse1` parse `lexed.settledSource`.

- `tokens lexed.settledSource.leaves = tokens lexed.leaves` for every
  source, with no `plain` hypothesis: the lengths agree by
  `settledOnceFlat` (`Syntax/GoodItemProofs.sw:300`), and the tokens
  are the lexer's by definition.
- `settledParsesGrammar1` is then `settledParsesKept1`'s one line for
  all sources. `settledParses1`, `settledParsesMoved1` and the case
  split go.
- Rule N and every theorem about `settledOnce`'s comments stay. The
  facts the parse-side theorems take about the leaves they parse
  (`settledGood`, `settledItemsQuiet`, the settled words, the comment
  texts, `unreturned`) are needed of `settledSource`: its comments are
  `settledOnce`'s and its tokens the lexer's, so each is either a
  transfer or the simpler proof that SW-4137 replaced (the one from
  token equality).
- The printer doesn't read a tree leaf's line start or column. The
  only definition files that read `lineStart`, `column`, `glued` or
  `lineIndent` are the lexer, the two parsers, `Settle.sw` and
  predicates about printed text (`Driver1.onLine1`, `NoteLines`,
  `Predicates1.hangs`, `SpeltSlots`, `StandsLine`, `WordsEdgeLine`)
  [source: grep]. And `formatKeepsProgram1` already equates the
  output's tree with the tidied source tree, which it couldn't if
  trees held layout.
- Idempotence: the output is `plain1`, so no comma starts a line and
  `settledSource` is `settledOnce` there.
- It holds for the whole language, not slice 1 only:
  `groupKeepsTokens` has no grammar hypothesis [reported, SW-4133
  checkpoint]. SW-4120 §7 said the last slice needs "rule N keeps the
  parse" for everything; this route gives it for nothing more.

It does not go against SW-4120 §7's warning (don't define the grammar
by the driver's parse): the grammar stays the language's parse of the
lexer's leaves. The driver moves towards it.

`parseFile lexed.settledOnce` appears 34 times in 10 files [source:
grep]: `Driver1` 3, `TopStatements` 8, `SettleParseProofs` 10,
`ParseSettledStatements` 3, `ParseWalkOthers` 2, `PlacedProofs` 2,
`UnreturnedProofs` 2, `OutputStatements` 2, `Passes` 1, `Tests/Shape1`
1.

### 1.4 The decision, and its cases

Route 3 changes what the proved tool's driver does, in one step: which
tokens it hands the parser.

- **Accepts less?** No case known. The new driver accepts every
  grammar source by proof. The old one accepts a source outside the
  grammar only by parsing marked leaves to a `within1` tree, and on
  every source measured the two parses agree.
- **Prints differently?** Only for a source with a last comma that
  starts its line, with its closer on the same line (`[1, 2⏎  ,]`,
  `(a, b⏎  ,)`), and only if the mark changes how that source parses.
  None found: the two parses agreed on all 14,349 generated sources
  with such a comma, on the indent grid of 2,260, and on must-accept
  cases 134 and 135 [reported, SW-4131 §4, SW-4176]. On such a source
  the old driver would be formatting a reading the language doesn't
  have.
- **The top theorems.** The three statements keep their text.
  `parse1`, which `formatKeepsProgram1` names, changes with the driver:
  "the program" becomes the parse of the source's own tokens.
- **What isn't offered.** A proof that the two drivers always agree.
  That is `settledParsesMoved1` plus a little, which is route 1.

My recommendation is yes. The lane's brief should say: no theorem
gains a hypothesis; `MustAccept1.sw`, `Grammar1.sw` and the three top
statements are not edited; `Settle.sw` gains one definition and loses
nothing; `Fmt.Tests` driver tests and `MustAccept1` are the tests to
run; the multi-line gate (the verifier's) should show no output change.

## 2. The checkpoint

### 2.1 The three statements [source]

| Theorem | Statement | Hypotheses |
|---|---|---|
| `formatAccepts1` (`Fmt/Accepts1.sw:28-30`) | `∃ out => formatWithin1 source = Ok out` | `inGrammar1 source = True` only |
| `formatKeepsProgram1` (`Fmt/TopStatements.sw:375-380`) | `parse1 source = Ok before ∧ parse1 out = Ok after ∧ after = before.tidy1.calmTop ∧ after.meaning = before.meaning` | `formatWithin1 source = Ok out` only |
| `formatIdempotent1` (`TopStatements.sw:405`) | `formatWithin1 out = Ok out` | the same, only |

`inGrammar1` (`Fmt/Grammar1.sw:158-164`) is: the source lexes, every
token is in the alphabet, the language's parser reads the lexer's
leaves, and the tree is `grammar1`. It doesn't mention the driver, rule
N or a layout test. So the first theorem hands the other two their
only hypothesis, for every source of the grammar: formatted, program
kept, idempotent. That is D3687.

`formatAccepts1`'s proof is the plan's shape (SW-4166 §1): one lemma
per driver test, each with no hypothesis beyond the lex, the alphabet,
the parse and `grammar1`: `alphabetOfAlphabet1`
(`SourcePlainProofs.sw:764`), `parsedSourcePlain1` (773),
`settledParsesGrammar1` (`SettleParseProofs.sw:320`), `parsedWithin1`
(`PlacedProofs.sw:349`, which takes `leavesWithin1`, supplied by the
first two). The only hole under it is `settledParsesMoved1`, whose own
hypotheses (the lex, the alphabet, the parse, `grammar1`, and the case
`plain1 = False`) hold of every source in that case: it is a case
split, not a condition.

### 2.2 Nothing narrowed today (D3688) [source: `git diff b8042192a HEAD`]

- **The driver only widened.** `leavesWithin1` lost `spelledPlain1`
  and went from `plain1` to `sourcePlain1` (implied by `plain1`,
  SW-4131 F8); `formatWithin1` lost the one-line refusal. Nothing was
  added (`Driver1.sw:52-64`).
- **`Grammar1.sw` and `Tests/MustAccept1.sw`** have one commit each,
  SW-4120's at 08:09. `Accepts1.sw`'s statement is SW-4120's; only the
  proof and doc changed.
- **The lexer, the parsers, `Settle.sw`, `Passes.sw`, `Meaning.sw`,
  `Walk.sw`**: no commit today. `Rules.sw` changed twice (SW-4155,
  SW-4159): printed layout for comment cases, reported byte-identical
  on the gate, and no refusal.
- **`within1` (`Slice1.sw`)** widened twice (names and numerals,
  SW-4125; `auto`, SW-4171) and tightened once: SW-4077 at 00:25 ties
  an infix node's kind to its operator text (`binaryText1`,
  `arrowText1`). That is a narrowing in form. It refuses nothing the
  parser builds, and that is now proved, not argued: `parsedWithin1`
  shows every `grammar1` parse is `within1`, and the infix clause is
  part of it. It merged before D3688 was given.
- **The top statements**: the diff of `TopStatements.sw` shows no
  changed hypothesis or conclusion on the two theorems; the only
  statement changes are the dropped `oneLine1` conjunct in `Formats1`
  and its lemmas.

### 2.3 Statements that changed or gained a hypothesis today

None can weaken a top theorem: each top statement is closed over its
own hypothesis alone, so an inner hypothesis that didn't hold could
only have stopped the proof. Listed because the brief asks, from the
merge log and the files; "holds of every parse" is from the lane
reports unless marked.

| Statement | Change | Holds of every grammar source? |
|---|---|---|
| `settledParsesMoved1` | new, open; takes the lex, alphabet, parse, `grammar1`, `plain1 = False` | yes, in its case [source] |
| `parsedWithin1` | takes `leavesWithin1` | yes: discharged in `formatAccepts1` [source] |
| 12 source theorems, SW-4137 | `plain1` became `sourcePlain1` | weaker hypothesis; `parsedSourcePlain1` proves it [source] |
| `anyFacts`, `elStep` (SW-4148, SW-4116) | take `shaped1` | yes: `tidiedFacts` derives it from the parse and `within1` [reported] |
| `ArgsHang`, `ItemsHang`, `LinkFacts` (SW-4147/8/9) | redefined with a per-item start; the old forms were false for commented items | definitions inside the proof; old facts still follow [reported] |
| `signArgHung`, `argumentHung`, `openStepsHung` (SW-4152, SW-4143) | restated; false as first written | callers in-file; `readsBackHung` unchanged [reported] |
| `Kept` (SW-4175) | conclusion gains `autoPlaced1 = False` | a stronger conclusion, proved [reported] |
| `readsBackHung` (SW-4126 fix) | def name `Lower` or `Upper` | a widening [source: commit 1ba400980] |
| `groupKeepsTokens1` | closed, statement SW-4129's | n/a [reported, SW-4133 checkpoint] |

### 2.4 Notes

1. **"Keeps the program" is about the driver's parse.**
   `formatKeepsProgram1` relates `parse1 source` and `parse1 out`, and
   `parse1` parses after rule N (`Driver1.sw:17-19`). `inGrammar1`
   speaks of `parseFile lexed`. The bridge between them is
   `settledParsesGrammar1` (`settled.withoutComments =
   file.withoutComments`), which is where the open goal sits. So for
   `[1, 2⏎  ,]` the theorem proved today says the output means what the
   driver's reading means, and that this is the language's reading is
   the unproved part. Nothing is wrong; it is the same open goal seen
   from the second theorem. But no theorem states the end-to-end
   sentence, and a reader of the three has to supply the bridge. See
   follow-up 2.
2. **The alphabet clause of `inGrammar1`.** Kept because the design
   states an alphabet. "No source is known whose tree is slice 1's with
   a token outside the alphabet" (`Grammar1.sw:155-157`) is not proved,
   so the clause may exclude sources. It is the grammar as Matt has it
   (D3687), not something a lane added. Unchanged since SW-4120.
3. **`sourcePlain1` is still a driver test.** Proved redundant on the
   grammar. Outside the grammar it can refuse a source that would
   otherwise format; that is outside D3687. Removing the test would
   need the settle theorems to hold without it, and isn't proposed.
4. **One-line vocabulary remains** (`onLine1`, `Decl.oneLine1` in
   `Driver1.sw:27-48`) for layers that still state it. Not a refusal.
   Worth deleting once nothing uses it.
5. **What this review did not do.** No check or test run. I read the
   statements and diffs named above, not the proofs under them; the
   kernel is the check for those.

## 3. Follow-ups (candidate tickets)

| # | What | Model (D3682) | Estimate |
|---|---|---|---|
| 1 | Route 3, after Matt's yes: `Lexed.settledSource`; driver and `parse1` parse it; token equality for all sources; the parse-side theorems re-pointed (10 files, 34 sites); `settledParses1`, `settledParsesMoved1` deleted; `formatAccepts1` closed. Top statements, grammar and must-accept file not edited | Opus: the driver's definition changes and about a dozen hypotheses are re-pointed | 45 min |
| 2 | A fourth top statement that reads D3687 in one sentence about the language's parser: `inGrammar1 source` gives `out` with `formatWithin1 source = Ok out`, `inGrammar1 out`, the language's parses of `source` and `out` with equal `meaning`, and `formatWithin1 out = Ok out`. Needs "the output is in the grammar" (from `within1` of the tidied tree and `Expr.grammarOfWithin1`) and the bridge both ways. Statement to be checked by the orchestrator | Opus for the statement, then routine | 30 min, after 1 |
| 3 | Re-run this checkpoint's section 2 after follow-up 1: one hole becomes none; confirm the three statements and `Grammar1.sw` untouched. Then slice 1 can be reported done | Fable (paper) | 10 min |
| 4 | Delete `settledOnceTokens`' `plain1` path and other lemmas route 3 orphans (`tokensBare` if unused) | DeepSeek | 10 min, after 1 |
| 5 | Delete the one-line vocabulary where nothing states it any more (note 4) | DeepSeek | 15 min |
| 6 | For slice 2's sketch: with route 3 the parse-after-rule-N fact needs no per-slice work. Without it, `lineIndent` after a marked closer feeds `|>`, `if` and `match` continuation tests (section 1.2); record this so nobody reintroduces the marked parse | note in the slice 2 sketch | 0 |

## Sources

- Code: `tools/fmt/src/Fmt/{Accepts1,Driver1,Grammar1,TopStatements,SettleParseProofs,PlacedProofs,SourcePlainProofs,Slice1,StandsLine,Predicates1}.sw`, `tools/fmt/src/Syntax/{Settle,Parser,GoodItemProofs,SettleProofs}.sw`.
- Reviews: `SW-4131-own-line-comma.md`, `SW-4133-two-run-checkpoint.md`, `SW-4120-grammar1.md` (§7), `SW-4166-carried-walk-plan.md` (headings only), `SW-4132-two-run-parse.md` (headings only).
- Tickets: SW-4183 and SW-4176 (ticket notes; SW-4183's lane report was not on the ticket).
- `git log --since=2026-11-19 -- tools/fmt`; `git diff b8042192a HEAD` for `Driver1.sw`, `Slice1.sw`, `TopStatements.sw`, `Grammar1.sw`, `Accepts1.sw`, `Tests/MustAccept1.sw`.
- Runs: the release formatter on three sources in the scratch folder (section 1.3).
