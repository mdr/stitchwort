# The last comma on its own line: what it takes to accept it (SW-4131)

Fable, 19 November 2026. Item 6 of the gap list in
[SW-4120's note](SW-4120-grammar1.md), under D3687 and D3689 (Matt,
19 Nov 2026): slice 1 is done when the driver accepts the whole grammar
in `Fmt/Grammar1.sw`, with nothing moved out.

How claims are marked: **[measured]** a run of mine today; **[source]**
read in the code; **[estimated]** my judgement. Nothing here rests on
how often a case occurs in the repo.

## Summary

**The problem.** The driver refuses a source where a last comma starts
its own line just before a closer, such as `[1, 2⏎  ,]`. The refusal is
the comma clause of `plain1`, which every comment-settling (rule N)
theorem about the source assumes.

**What I found.** The refusal is a shortcut taken in two proof lanes,
not a gap in what is true. Since SW-3964 the driver moves such a
comma's comments above the closer *before* rule N runs, and leaves the
comma bare. After that step the old trouble (spike K1) can't arise.
Every conclusion the settle proofs and the printer proofs draw still
holds with the comma on its own line: on 19,943 sources in the
grammar, 14,349 of them with such a comma, no fact failed [measured]. Only the hypothesis `plain1` has to be replaced by a
weaker one, and one helper fact ("the step moves no token") restated,
because the closer after such a comma is marked as starting its line.

**The change.** One Sonnet proof lane of about 40 minutes [estimated],
in the three settle-proof files and their callers. The stop rule does
not apply: comment placement is not restated in any layer. I recommend
keeping the case in slice 1, as D3689 has it. There is no decision for
Matt in this note.

**What it should do.** The driver formats every source with a last
comma on its own line, and the three top theorems cover them. Of the
five must-accept tests that fail for this cause, three pass after the
lane and two wait only for the multi-line work (they fail the one-line
test too) [measured: the five sources through the driver with the new
test].

**One thing this note found beside its task.** `plain1`'s other clauses
(no `->` directly before a comma, a closer or another `->`; no comma or
closer first) refuse no grammar source [measured: every token order up
to five tokens]. But nothing proves that yet, and the acceptance
theorem needs it. SW-4120's gap list didn't count it. It is one more
parser fact, section 5.

## 1. What rule N does with such a comma today

The driver doesn't hand the lexer's leaves straight to rule N. It
first runs `withBareLastCommas` [source: `Syntax/Settle.sw`,
`commaMoved`, `withBareLastCommas`, `Lexed.settledOnce`]. For each
comma directly before a closer, with an item before it:

| What the comma has | Where it goes |
|---|---|
| Comments on their own lines above it | Above the closer, before the closer's own |
| A comment after it, the comma not starting its line | To the end of the item before it |
| A comment after it, the comma starting its line | Above the closer, after the comma's own-line comments, keeping the comma's blank line |
| No comment after it, the comma starting its line, the closer with own-line comments | The closer's first own-line comment gets one blank line above it |
| The comma itself | Stays, with no comment and no blank line, still starting its line if it did |
| The closer | Is marked as starting its line if the comma did |

Then rule N runs. Its first pass, which moves a comment after a closer
back to the code before it, walks past the bare comma and never leaves
a comment on it: if the comma starts its line, so does the closer, and
the walk stops on the closer first. Its second pass finds nothing on
the comma to carry. The tidy pass P2 then drops the comma from the
tree. So `[1, 2⏎  , -- c⏎  ]` prints as the list with `-- c` on its own
line above the `]`.

Three sources and what the driver prints for them once the `plain1`
test is out of the way [measured]:

```
def x: T := [1, 2            def x: T := [1, 2]
  ,]

def x: T :=                  def x: T := [
  [ 1                          1,
  , 2 -- two                   2 -- two
  -- above the comma           -- above the comma
  , -- after the comma         -- after the comma
  ] -- after the closer      ] -- after the closer

def x: T := [(1, 2           def x: T := [
    , -- c                     (
    )                            1,
  ] -- d                         2
                                 -- c
                               ) -- d
                             ]
```

### Why it was refused

Spike K1 looked at rule N *without* the bare-comma step. There a comma
that starts its line keeps its trailing comment through the first pass,
and the second pass moves it above the closer. A later closer whose
comment stayed put because "the line before ends with a comment" then
no longer has that reason, so the result is not "homed": running rule N
again would move that comment. In `[(1, 2⏎ , -- c⏎ )⏎ ] -- d` the
`-- d` is left on the `]` [measured: `homedBehind` of `lexed.settled`
is false on this source and on 52 of the 20,300 generated ones].

SW-3964 (18 Nov, 15:15) added the bare-comma step, which removes the
trouble: the comma's comment is above the `)` before rule N starts, and
`-- d` goes to the `)`. But the two proof lanes that followed assumed
`plain1` to save a case:

- SW-4006 (`bareSettles`): "under `plain1` no last comma starts its
  line, so making them bare moves no token" [source:
  `SettleBareProofs.sw:1344`]. Its three hard lemmas (`backWalkDrop`,
  `commaCarryDrop` and the walk under them) do not assume it. They carry an
  invariant, `barish`, that already says "a bare last comma starts a
  line only if its closer does" [source: `SettleBareProofs.sw:124`].
- SW-4022 (`onceSettledProved`): "a last comma that is laid out and
  `plain` starts no line and holds no own-line comment, so only its
  trailing comment moves" [source: `SettleOnceProofs.sw:145`].

SW-4018, written between the two, recorded `plain1` as "a real
hypothesis, not one a lane can remove", and the driver got the test. That reading was of K1's
finding, which SW-3964 had already made out of date.

## 2. What the proofs assume, and where the comma clause is used

`plain1 (tokens lexed.leaves)` is a hypothesis of 14 theorems and a
test in the driver [measured: grep]. Two of the 14, `settledHomed` and
`settledIdempotent`, are only ever applied to leaves with no last
comma, and keep it. The other 12 are about the source. The comma clause itself is used in
six places [source: every use of `plainNoStart`, and of the second
conjunct of `plainFrom`]:

| Where | What the clause gives | True with the comma on its own line? |
|---|---|---|
| `withBareRTokens`, so `tokensBare` (`SettleBareProofs`) | making last commas bare changes no token | **No**: the closer gains a line start. Kinds, texts and columns are kept |
| `laidWithout` (`SettleOnceProofs`) | the leaves without their last commas are laid out as the lexer lays them out | yes; needs the other branch of `commaMoved` |
| `plainWithout` | those leaves are `plain1` | yes, in the strict sense: no last comma is left |
| `allTokensWithout` | a test true of every token still is | yes, for a test that doesn't read the line start (both uses: the alphabet, and text agreeing with kind) |
| `textsWithout` | a test true of every comment text still is | yes: the same texts, in the same order |
| `endsTransfer` (`SettleProofs`), under `settledHomed` | a line that ends with a comment before passes 2 to 5 still does | used only on the leaves *without* last commas, which are strictly `plain1` |

Everything downstream takes the conclusions, not the clause:
`settledGood` and `settledOnceTokens` (`GoodItemProofs`),
`onceTextsPlain` (`OnceUnreturnedProofs`), `onceWordsSettled1`,
`parseCarriesSource`, `parseSettledSource` and their `Proved` forms
(`ParseSettledStatements`, `ParseWalkOthers`), `parsedUnreturned` and
`commaUnreturned` (`Fmt/UnreturnedProofs`), and the top theorems
(`Fmt/TopStatements`).

**The printer's side assumes nothing about the source's commas.** It
works from the tree after P2, which has no comma, and from the tree
facts `settled1`, `shaped1`, `lexical1`, `commaFree` and `unreturned1`.
`printedPlain1` proves the *output* is `plain1` (no comma starts a line
there); that theorem and the strict `plain1` stay as they are.

## 3. The restated facts

### The hypothesis

`plain1` stays, for the output and for the leaves without last commas.
The source's theorems take a weaker test beside it:

```
--| `plain1` with a last comma allowed to start its line: a comma that
--| starts its line comes before a comma or closer only as a last
--| comma, before a closer and after an item. `before` is the kind of
--| the token before `first`.
def sourcePlainFrom (before: Option Tok): List Token → Bool
  | [first, second, ..rest] =>
    (!(first.kind == Arrow) || !arrowFollow second.kind)
      && (!(first.kind == Comma && first.lineStart)
        || !passableKind second.kind
        || (second.kind.isCloser
          && (before.map (kind => !(kind == Comma) && !kind.isOpener) |> .getOrElse False)))
      && sourcePlainFrom (Some first.kind) [second, ..rest]
  | _ => True

def sourcePlain1 (tokens: List Token): Bool := match tokens with
  | [] => True
  | [first, .._] => !passableKind first.kind && sourcePlainFrom None tokens
```

- It is `plain1` or K1's case, and nothing else: `plain1 tokens = True`
  gives `sourcePlain1 tokens = True` clause by clause, so the driver
  accepts strictly more and no theorem gains a condition (D3688).
- The "after an item" part mirrors `hasItem`, which decides whether the
  driver treats a comma as a last comma at all. `[⏎,]` and `[1,⏎,]`
  stay refused by the test; neither parses.

### The facts

Each keeps its conclusion; `plain1` becomes `sourcePlain1` in the
hypothesis. `once` is `lexed.settledOnce`, `without` is the leaves
after `withoutLastCommas`.

| # | Fact | Change |
|---|---|---|
| F1 | `plain1 (tokens without) = True` | new hypothesis; replaces `plainWithout`'s |
| F2 | `laidOut False without = True`, given it of the lexer's leaves | new hypothesis; one more branch |
| F3 | the comment texts of `without` are those of the source, in order | as F2 |
| F4 | `bareSettles`: `once`, its last commas dropped, is rule N on `without` | new hypothesis; the proof's only uses of `plain1` are the `->` clause and `tokensBare` |
| F5 | **restated**: `tokensBare` and `settledOnceTokens` say the tokens are equal. Now: equal once every line start is forgotten, `(tokens once.leaves).map flat = (tokens lexed.leaves).map flat`. If the exact change is wanted: a line start differs only on a closer directly after a comma that starts its line, from false to true | the one statement that changes |
| F6 | `onceSettledProved`: the words of `once` are settled (closers homed, `->` bare, comment texts trimmed) | new hypothesis only |
| F7 | `onceTextsPlain`, `settledGood`, `parseCarriesSource`, `parseSettledSource`, `parsedUnreturned`, `commaUnreturned` | new hypothesis only; `settledGood` uses F5, and reads only kinds and texts |
| F8 | `plain1 tokens = True` gives `sourcePlain1 tokens = True` | new, one line per clause; for the output, so `printedPlain1` still feeds the driver's test in the idempotence proof |

F5 is where a careless lane could go wrong: `tokensBare` is false as
stated for this case, and the proof must not be forced by narrowing.
Nothing downstream needs line starts to be equal [source: the two
consumers are `bareSettles`, for the alphabet and the `->` clause, and
`settledGood`, for spelling and fixed texts].

## 4. The checks

A scratch module (deleted before the commit) computed, for each source,
the grammar test, both hypotheses, F1 to F6 as booleans, and then the
whole chain with the driver's `plain1` test swapped for `sourcePlain1`
and its one-line test left out: the two parses agree (the lexer's
leaves and `once`), the tree is in slice 1 and `settled1`, the words
are carried, the five tree facts hold after tidying, the printed text
hangs and stands, lexes to the leaves it was printed from, is `plain1`,
reads back, formats to itself, keeps the meaning and keeps every
comment's text in order.

| Set | Sources | Pass the new test | In the grammar | In the grammar with an own-line last comma | Failures |
|---|---|---|---|---|---|
| Generated, "focus": nine brackets in ten end in a comma, three in four of those on their own line, a comment above, after or before it a third of the time each, nested to depth 3, in types and values | 12,300 | 12,300 | 10,193 | 8,566 | 0 |
| Generated, "mixed": the same shapes with fewer last commas and comments | 8,000 | 8,000 | 7,303 | 3,509 | 0 |
| Indent grid: eight shapes (plain, nested, in a call, in a type, with comments), the comma at columns 1 to 6, the item before it at columns 1 to 6, the closer after 0 to 3 spaces or on the next line at columns 1 to 6 | 2,880 | 2,880 | 2,260 | 2,260 | 0 |
| Hand cases, with K1's own and SW-3964's two families | 12 | 12 | 12 | 11 | 0 |
| Every order of up to five of `a` `,` `->` `(` `)` `[` `]`, as a type and as a value, on one line | 39,214 | 28,766 | 172 | 0 | 0 |
| Every such order of up to four with a comma, each comma starting a line | 2,812 | 1,790 | 3 | 3 | 0 |
| **Total** | **65,218** | **53,748** | **19,943** | **14,349** | **0** |

All [measured]. What was computed on which:

- **On all 53,748 that pass the new test**, in the grammar or not: F1
  to F6, that rule N run again on `once` changes nothing, and that
  rule N keeps every comment text in order. No failure. So the facts
  follow from the hypothesis, not from the parse.
- **On all 19,943 in the grammar**: the whole chain above. No failure.
- **On all 65,218**: a source in the grammar passes the new test, and
  passes the `->` and first-token clauses; a source that is `plain1`
  passes the new test. No exception.
- **The `->` clauses refuse no grammar source in the exhaustive sets**:
  of the 39,214 token orders, 172 are in the grammar and all 172 are
  `plain1`. `(A -> , B)`, `(A ->)` and `[A -> -> B]` do not parse.
- **The 620 grid sources outside the grammar** are the ones the
  language itself refuses, such as a `,` at its item's column.

What the checks are not: they are computations on generated sources,
not proofs. The generators use plain names, eight operators, at most
two declarations and depth 3; the random sets are samples, and only the
two token-order sets are exhaustive.

## 5. The lanes

Estimates are from the two lanes that wrote these files: SW-4006
(Sonnet, 78 theorems, 35 minutes) and SW-4022 (Sonnet, 83 theorems,
20 minutes) [source: their tickets' model-result lines]. The work here
is smaller than either: one more case in four lemmas, one restated
helper, and a hypothesis renamed through the callers.

| Lane | What | Model (D3682) | Estimate | Files |
|---|---|---|---|---|
| C1 | `sourcePlain1` and F8; F1 to F7 with the new hypothesis; the driver's `leavesWithin1` tests `sourcePlain1`; the top theorems re-proved with their statements unchanged; the three must-accept tests that fail only for this cause pass | Sonnet: a case split in passes that keep a property, statements fixed by this note | 40 min | `Syntax/SettleProofs.sw` (two definitions and F8 added), `SettleBareProofs.sw`, `SettleOnceProofs.sw`, `OnceUnreturnedProofs.sw`, `GoodItemProofs.sw`, `ParseSettledStatements.sw`, `ParseWalkOthers.sw`; `Fmt/Driver1.sw`, `UnreturnedProofs.sw`, `TopStatements.sw`; comments in `OutputStatements.sw` |
| C2 | Every parsed source is `sourcePlain1`: from `parseFile lexed = Ok file` and the alphabet, no `->` is directly before a comma, closer or `->`, the first token is neither, and a comma follows neither a comma nor an opener. Then the test leaves the driver, or the acceptance proof uses the fact | Opus: a new parser fact, as `auto`'s is | 45 to 90 min, low confidence | `Syntax/ParseCarries*.sw` or a new file beside them; `Fmt/Driver1.sw`, `Accepts1.sw` |

**C1 is all of item 6.** SW-4120 estimated 3 to 4 lanes for it; it is
one, and this note was the sketch.

**C2 is not new with this item.** It is owed for `plain1`'s `->` and
first-token clauses whatever happens to the comma clause, because the
acceptance theorem has only the grammar on its left-hand side and the
driver tests `plain1`. SW-4120's item 8 said the driver's remaining
tests would be the alphabet and `within1`; this is a third. I'd fold
its statement into the sketch for item 7 (rule N keeps the parse),
since both are facts about what a successful parse says of the tokens,
and both may be a walk over the parser. The parser proofs carry the
tree's *words*, which leave commas out, so the comma parts need the
comma-list lemmas (`readsCommaListFrom`) to say more than they do
[source: `ParseCarries.sw:387`]. That is why the estimate is wide.

**For item 7.** This is the one place rule N changes a token: the
closer's line start. The parser does read line starts of closers
[source: `Parser.sw` `startsBlock`, `ranOutOn`, `blockEnd`]. On every
generated source and the whole indent grid the parse of `once` equalled
the parse of the lexer's leaves [measured, above], so the fact item 7
needs looks true here too, but its proof must go through this change
and cannot be "the tokens are the same".

### Order and clashes

1. C1 can start as soon as SW-4125 (name spelling) has merged. Both
   edit `Driver1.leavesWithin1`, `GoodItemProofs.settledGood` and the
   hypothesis lists that carry `spelled` and `plain` side by side in
   `ParseSettledStatements`, `ParseWalkOthers`, `UnreturnedProofs` and
   `TopStatements`. Running them together would conflict on the same
   lines.
2. C1 doesn't touch SW-4126's files (the new `Syntax/ReadBackHung*`
   skeleton, `PrintedGroup`, `readsBackDecl1`). If SW-4126 edits
   `TopStatements.sw` the overlap is a few hypothesis lines.
3. SW-4127 (`endsAtom`) is merged and touches none of these files.
4. C2 after C1, and after or with item 7's sketch.

### What C1's brief should say

- The statements in section 3, and that `plain1` is not redefined.
- `tokensBare` is false for this case: restate it as F5, don't add a
  condition to it.
- No theorem gains a hypothesis; `plain1` becomes `sourcePlain1` and
  nothing else. `MustAccept1.sw` is not edited.
- Tests to run: `Fmt.Tests.MustAccept1` (three more pass), and checks
  of the namespaces it edits.

## 6. The stop rule

It doesn't apply. The settled facts (`settled1`, `homedBack`,
`arrowsBare`, the comment-text facts) are unchanged, and no printer,
read-back or tidy proof is touched. So there is no case here for
moving the own-line comma to slice 3, and I don't set that option out.

## Findings

- **The acceptance theorem needs "a parsed source is `plain`"**, which
  no gap item counts (lane C2 above). Worth a ticket now, linked to
  item 7's sketch.
- **SW-4018's "`plain1` is a real hypothesis, not one a lane can
  remove"** was out of date when written: it cites K1, and SW-3964 had
  changed the driver an hour and a half earlier. A statement note that cites
  an older spike should rerun the spike's failing case on the current
  code.
- **`OutputStatements.holdsOnExample`-style conjunctions name `plain1`
  of the output**; they stay true and need no change.
- **Not a failure, for the record**: in K1's shape the driver moves
  `-- d` from after the `]` to after the `)` (third example above).
  That is rule N's first pass doing what it does for any closer, and
  what the Rust formatter does.

## Sources

- `tools/fmt/src/Syntax/Settle.sw`, `SettleProofs.sw`,
  `SettleBareProofs.sw`, `SettleOnceProofs.sw`,
  `OnceUnreturnedProofs.sw`, `GoodItemProofs.sw`,
  `ParseSettledStatements.sw`, `ParseWalkOthers.sw`, `ParseCarries.sw`,
  `Parser.sw`; `Fmt/Driver1.sw`, `Grammar1.sw`, `UnreturnedProofs.sw`,
  `TopStatements.sw`, `OutputStatements.sw`.
- `docs/reviews/SW-4120-grammar1.md` item 6,
  `SW-4119-slice1-review.md`, `SW-4018-parser-statements.md` §5.3;
  `docs/proposals/self-hosted-fmt-s1-sketch.md` §3.4; tickets SW-4006,
  SW-4022, SW-3998.
- Runs: `stitchwort run` of a scratch module (deleted) over the sets in
  section 4. The generators and results are in the lane's scratch
  folder, not the repo.
