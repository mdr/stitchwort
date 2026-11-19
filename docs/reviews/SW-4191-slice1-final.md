# Slice 1, final checkpoint after SW-4183 (SW-4191)

Fable, paper review, 19 Nov 2026, against `main` at 3c70e3449 (SW-4183
merged as 8aafcab42). Compared with `main` at 9395074ab, the commit the
SW-4184 checkpoint read. Nothing was built or checked.

How claims are marked: **[source]** read in the code or a `git diff`
today; **[reported]** from SW-4183's report, as the brief gives it;
**[estimated]** my judgement.

## Verdict

**Slice 1 meets D3687, on the condition that the orchestrator's check of
`main` confirms "no open goals".** `formatAccepts1` is stated over the
whole of `Grammar1` with `inGrammar1 source = True` as its only
hypothesis, and `formatKeepsProgram1` and `formatIdempotent1` each take
only `formatWithin1 source = Ok out`. None of the three statements, the
grammar or the must-accept file changed since SW-4184. The one open goal
then, `settledParsesMoved1`, is deleted, not proved around: the tokens
the driver parses are now the lexer's for every source, by a theorem
with no hypothesis. I found no `?`, `axiom` or `trusted` in
`tools/fmt/src` [source: grep]. That the project checks is [reported];
I could not run it.

Nothing accepts less (D3688): the driver's tests are the same three, and
only its `Err` texts changed.

**Owed before telling Matt it is done:**

1. The background check of `main` passing (the kernel is the check on
   the proofs; this review read statements and diffs).
2. One stale doc comment on the acceptance theorem,
   `Fmt/Accepts1.sw:22-23`: "Proved but for one open goal it relies on,
   `settledParsesMoved1` ...". The goal no longer exists. It is a
   comment, not the statement, but it sits on the theorem Matt will be
   pointed at and says the opposite of the truth. I did not edit it:
   lanes don't edit an acceptance theorem's file without being asked
   (CLAUDE.md, "Lane agents"). A two-line deletion for the orchestrator.

**Not blocking:** the fourth top statement (SW-4184 §3, follow-up 2).
See question 5.

## 1. The three statements and the grammar

Unchanged in text [source: `git diff 9395074ab HEAD`].

| Item | Where | Change since SW-4184 |
|---|---|---|
| `formatAccepts1` | `Fmt/Accepts1.sw:29-31` | statement and proof unchanged; the only diff is the three doc lines of item 2 above, added in SW-4185's commit 164d3cb16 (true then, stale since SW-4183) |
| `formatKeepsProgram1` | `Fmt/TopStatements.sw:375-380` | none |
| `formatIdempotent1` | `Fmt/TopStatements.sw:405` | none |
| `TopStatements.sw` as a whole | | one comment line (a deleted lemma's name dropped, line 110) |
| `inGrammar1`, `Grammar1.sw` | `Fmt/Grammar1.sw:158-164` | no diff |
| `Tests/MustAccept1.sw`, `Slice1.sw` (`within1`), `Meaning.sw` | | no diff |

No new hypothesis on the path. Each top statement is closed over its own
single hypothesis, so an inner lemma's hypothesis can't weaken it; and
the inner changes all go the other way [source: the merge's diff]:

- `settledOnceTokens` (`Syntax/GoodItemProofs.sw:282`) lost `plain1`:
  `tokens lexed.settledOnce.leaves = tokens lexed.leaves` for every
  `lexed`.
- `settledParses1` (`Fmt/SettleParseProofs.sw:287-293`) lost `plain1`.
- `settledParsesGrammar1` (`SettleParseProofs.sw:297`) keeps its
  statement; its proof is now one call, with no case split.
- `settledParsesMoved1`, `settledOnceFlat`, `tokensBareFlat`: gone; no
  mention left in `tools/fmt/src` but the stale comment.
- The other changed lemmas (`homeFromTokens`, `stepsPlain`, `homeQuiet`,
  `settledWithKeepsTokens`, `settledWithQuiet`) gained a `bareLast`
  parameter they hold for both values of, or were pinned to `False`
  where they speak of `Lexed.settled`. No statement gained a condition.

SW-4184's note 1 ("keeps the program" is about the driver's parse, and
the bridge to the language's parse was the open goal) is closed in
substance: `settledParsesGrammar1` now proves, for every grammar source,
that the driver's tree is the language's tree but for comments.

## 2. `bareSettles` up to line starts; the marked copy

**The restatement** (`Syntax/SettleMarkProofs.sw:559-563`): same two
hypotheses as before (`alphabet1`, `sourcePlain1`), same `end` equation;
the leaves equation is now between the two sides mapped through
`Leaf.unstarted` (line start set to `False`). That is weaker by exactly
the closer's line start, which is the point: `settledBare` deletes the
comma, so its closer starts the line; the formatter keeps the comma and
the lexer's token.

**Its users lose nothing.** There are two, and both only ever took the
words from it [source: grep, and the merge's diff of each]:

- `onceSettledProved` (`Syntax/SettleOnceProofs.sw:1360`, use at 1419)
- `onceTextsPlain` (`Syntax/OnceUnreturnedProofs.sw:67`, use at 104)

Each now adds two steps through `wordsOfUnstarted`
(`SettleOnceProofs.sw:1288`: a line start is no part of a word). Neither
statement changed; only their proof bodies did. `CommentsKept`
(`Fmt/Meaning.sw:289`) is stated on `settledBare` itself, which is
untouched in meaning: `withoutLastCommas` used `commaMoved` with the
mark and now uses `commaDeleted`, which is `commaMoved` plus the same
mark (`Syntax/Settle.sw:333-336`).

**The marked copy is the old statement, kept as a proof device.**
`withMarkedLastCommas` (`Syntax/SettleBareProofs.sw:1149-1154`) is
line for line the old `withBareLastCommas` (it calls `commaDeleted`
where the old one called the marking `commaMoved`), `settledMarked`
(1672) is the old `settledOnce`, and `markedSettles` (1689-1692) is the
old `bareSettles` with those names. `onceMarked`
(`SettleMarkProofs.sw:533-536`) ties the new `settledOnce` to it up to
line starts, under `alphabet1` only. `settledMarked` and
`withMarkedLastCommas` are named only in those two proof files; the
driver imports neither [source: grep; `Fmt/Driver1.sw:10-14`].

A useful by-product: `onceMarked` is a proof that the new tidying step
puts every comment where the old one did, for every source that passes
the alphabet test. So "output byte-identical on 10,476 sources"
[reported] is, for comment placement, a theorem; a source's output can
differ from before only if the old mark changed its parse, and then the
new reading is the language's (SW-4184 §1.4).

## 3. Is the bookkeeping inside the tidying step?

Yes [source].

- No token leaves `settledOnce` changed: `settledOnceTokens`, with no
  hypothesis. `commaMoved` no longer calls `startingLine`
  (`Settle.sw:318-329`); `withBareLastCommas` (354-359) only empties the
  comma's trivia and moves comments.
- The line-start reading lives in one function, `startsWalk`
  (`Settle.sw:125-132`), called from one place, `stepsBack` (142). In
  rule N the only other read of a line start is a comma's own (line
  106), which the mark never touched. So the old mark had exactly one
  reader, and that reader now computes it.
- `Lexed.settled` is `settledWith False` (`Settle.sw:289`), and
  `startsWalk False current _` is `current.token.lineStart` (126): the
  old code, definitionally. `crates/fmt` has no diff in the merge. The
  Rust mirror and its comparison test (`Fmt/Tests/Passes.sw:124`) are
  untouched.
- `startsWalk True` matches the old mark's condition: closer, previous
  leaf a comma that starts its line, an item before it (`hasItem`, which
  reads one leaf's kind, so settled or unsettled leaves give the same
  answer). Every such comma is one `withBareLastCommas` made bare, since
  its pattern is the same three tests (355).

## 4. Does anything accept less (D3688)?

No [source: `git diff 9395074ab HEAD -- Fmt/Driver1.sw`].

`formatWithin1` (`Fmt/Driver1.sw:98-105`) at SW-4184's time and now:

| Step | Then | Now |
|---|---|---|
| lex fails | `Err message` | `Err ("lex error: " ++ message)` |
| `!leavesWithin1 lexed.leaves` | fixed text | `Err (leavesRefusal1 ...)` |
| `parseFile lexed.settledOnce` fails | `Err message` | `Err ("parse error: " ++ message)` |
| `!parsed.within1` | fixed text | `Err (constructRefusal1 parsed)` |
| otherwise | `Ok parsed.tidy1.printed1` | the same |

The conditions are the same expressions; `leavesWithin1` (line 30),
`tidy1` and `parse1` are unchanged. SW-4185's new functions
(`leavesRefusal1`, `misplacedFrom1`, `Decl.outside1`,
`constructRefusal1`) are called only inside `Err` arms. Its deletions
are theorems and one-line vocabulary nothing ran (`onLine1`,
`Decl.oneLine1` were already not a refusal at SW-4184, note 4); no
definition the driver calls changed. The driver tests moved from
"starts with `outside slice 1`" to exact messages
(`Fmt/Tests/Driver1.sw`), which is stricter on the text only.

SW-4183 changes what the driver parses on one family of sources (a last
comma starting its line, closer on the same line): the closer's token is
now the lexer's. That was Matt's decision (D3690), and for grammar
sources acceptance is proved. Outside the grammar, a source the old
marked parse happened to read as `within1` and the true parse doesn't
would now be refused; none is known, and it is the case SW-4184 §1.4
put to Matt.

## 5. Does slice 1 meet D3687?

Yes, subject to the two items under the verdict.

- Acceptance over the whole grammar: `formatAccepts1`, hypothesis
  `inGrammar1` only; `inGrammar1` doesn't mention the driver, rule N or
  a layout test.
- Meaning kept and idempotent: the other two theorems, whose single
  hypothesis `formatAccepts1` supplies for every grammar source.
- No open goal under any of them [source: grep; reported: the check].

**The fourth top statement does not block.** It would say D3687 in one
sentence about the language's own parser. Everything it needs is now
proved except "the output is in the grammar" as a stated lemma; it adds
a reading aid, not a missing fact. Worth doing next, with its statement
checked before proof (it is a top statement).

SW-4184's standing notes 2 and 3 are unchanged and are the grammar as
Matt has it: the alphabet clause of `inGrammar1`, and `sourcePlain1` as
a driver test that is redundant on the grammar.

## Small findings (tickets, none blocking)

| # | What | Size |
|---|---|---|
| 1 | Delete the stale lines `Fmt/Accepts1.sw:22-23` | 1 min, orchestrator |
| 2 | `settledPlaced1` (`Fmt/SettleParseProofs.sw:310`) still takes `plain1` and has no caller left; delete it, or restate it under `sourcePlain1` if slice 2 wants it | DeepSeek, 10 min |
| 3 | `tools/fmt/NOTES.md:1399-1400` describe `bareSettles` "under `plain1`" and "searched, not proved"; `SettleParseProofs.sw:6` has an over-long doc line from the edit | DeepSeek, 5 min |
| 4 | `settledParsesGrammar1`'s `source`, `lexes` and `alphabet` arguments are now unused by its proof; harmless, could be dropped with its one caller | with 2 |
| 5 | The fourth top statement (SW-4184 §3 item 2) | Opus for the statement, then routine |

## What this review did not do

No build, check or test. I read the statements, the definitions in
`Settle.sw`, and the diffs named above; not the 588 lines of
`SettleMarkProofs.sw` beyond its definitions, `onceMarked` and
`bareSettles`. The kernel is the check for those.
