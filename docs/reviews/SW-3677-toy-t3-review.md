# SW-3677: review of Toy++ T3 (rule N)

Opus, 17 November 2026. This is the D2364 review of T3a (SW-3675, merge
`359d1f8fc`) and T3b (SW-3676, merge `36277b392`), which weakened
theorems. I compared every theorem statement in `tools/toyfmt/src` before
and after (`359d1f8fc^1` against `36277b392`), extracted by script: 98
statements changed, 25 were removed and 269 were added. Most changes come
from `Item` becoming `Expr`, `Parameter` becoming `ParameterGroup`, or a
`…Lays` becoming a `…Puts`. I read the rest one by one.

**[run]**: `stitchwort check Toy.Fmt.KeepsComments` in the worktree
(8 namespaces, clean); `stitchwort axioms` on `printParses`,
`formatIdempotent` and `formatKeepsComments` (none used); and twelve
small sources through `parse` (via `dumped`) and `toyfmt`, listed under
question 2.

## Verdict

**T4 can start: yes.** Nothing is wrong. No top theorem changed its
statement, none gained a hypothesis the parser can't meet, and the
weakened statements are forced by rule N. What they dropped is
recovered at the level that matters (`Tucks`, `printedWords`,
`formatKeepsComments`). The findings are three wording fixes and one
unproved claim in a doc comment, and none of them blocks T4. Finding 5 is
something T4 has to know about, not something to fix.

## Findings

| # | Severity | Where | T4 depends? |
|---|---|---|---|
| 1 | wording | `printedTokens` doc, `src/Toy/Fmt/PlaceProofs.sw:321-325` | no |
| 2 | wording | `lexFits` name, `src/Toy/Fmt/CarryLex.sw:257` | no |
| 3 | wording (unproved claim) | `Comments.closing` doc, `src/Toy/Syntax/Ends.sw:72-76` | no |
| 4 | weaker than needed (open, unused) | `settledIdempotent`, `plus/src/Proofs.sw` only | no |
| 5 | note for T4 | `Parsed` is stronger: `settledCloser` in `Shaped`, `ShapedType`, `ShapedParameters`, `ParsedHeader` | yes: `tidyParsed` must keep it |

**1. `printedTokens`' doc still makes the claim T3a dropped.** The
statement now says only that the text is the printed pieces joined, and
that it lexes to the tokens `placed` gives of them. Its doc goes on to say
that "the pieces between whose layout are the file's tokens and comments
in order", which is the dropped clause `wordsOf (printedPieces …) =
wordsOf file.pieces`, and false under rule N (`[a, b] -- c` prints
`-- c` after `]`). It should say: "…lexes to the tokens `placed` gives of
its printed pieces, each token of the kind its text spells…; how the
pieces' words stand to the file's is `printedEvents` (`Tucks`)."

**2. `lexFits` no longer states `Parse.Fits`.** Its statement is now
`List.All Tidy lexed.tokens ∧ Rising lexed.tokens`. That is the content
of the old `Lexer`, so nothing was lost: the old statement unfolded to
exactly this. But `Lexer` is now `Settling ∧ Rising`, which the lexer's
own tokens don't satisfy (a comma may hold comments), and the theorem
that gives `Fits` is `settledFits`. The name promises what only
`settledFits` delivers. It should be renamed `lexTidy` (or
`lexTidyRising`); its doc is already right.

**3. "On settled tokens there is none" is unproved, but the doc states it
as fact.** `Comments.closing`'s doc says the case where it moves a comment
never arises on settled tokens. SW-3676's notes and SKETCH-PLUS ("Neither
fires on settled tokens, and that is not proved in either") say it is not
proved, but the code's doc doesn't. It should read: "…On settled tokens
there should be none (not proved; the goldens and probes are the
evidence), so this is meant to change nothing the parser reads; either
way it makes `settledCloser` a fact about the tree." Soundness doesn't
rest on the claim (question 2). If the claim is wanted as a guarantee,
the cheapest form is a test over the goldens, `plus/inputs` and the
disturber's outputs, checking that no closer in the parsed tree has an
`above` comment that is the same token's trailing comment in
`lexed.settled`. A proof needs "the last spelled token's trailing comment
is `endsWithComment`" for each part of the tree, about one lemma per
part, which is roughly the size of T0's `receive` families.

**4. `settledIdempotent` is still open** (only in `plus/src/Proofs.sw`).
No theorem uses it: `formatIdempotent` goes through `printParses`. It
belongs with the rule-N facts the real formatter will want (SKETCH-PLUS,
T3a finding 3, estimates about 15 lemmas). Leave it for T7 or a backlog
ticket. It is not needed for T4.

**5. For T4: `Parsed` now includes rule N's normal form.** `Shaped` has
`settledCloser inner.endsWithComment close` for `Bracketed`, and
`settledCloser (itemsEndWithComment open items) close` for lists and
calls, where `BareLastItem` used to be. `ShapedType` and
`ShapedParameters` have the same, and `ParsedHeader` gained it.
`parseParsed` proves it of every parse result, by construction through
`Comments.closing`, so `printParses` is not narrowed. But every tidy pass
must now keep it (`tidyParsed`, T0's `walkKeepsSettled`):

- P2 (trailing commas, new at T4): `itemsEndWithComment` and
  `groupsEndWithComment` ignore the comma, which is right, because rule N
  moves a closer's comment past a bare trailing comma (`movesPast` takes
  commas). The calm reader (`Fmt/CalmProofs.sw`) and `FileEvents` will
  need the trailing comma's event. The proposal's `bare: NoTrailingCommas`
  hypothesis on `printParses` comes back here, as §3.3 says.
- P3 (brackets, T5): `settledCloser` is monotone in `before`, so dropping
  a comment-free pair inside another can only turn a `before` from
  `False` to `True`. That direction keeps the outer closer settled.

## The questions of the brief

### 1. Changed, removed and weakened statements

These are the ones that changed in substance. All the others changed only
a type or a predicate name.

| Theorem | Change | Forced? | Recovered by |
|---|---|---|---|
| `printedTokens` (`Fmt/PlaceProofs.sw:326`) | drops `wordsOf printed = wordsOf file.pieces` | yes: false once a rule uses `Closing`; nothing read it (`printedPlaced` ignored it) | `printedEvents` with `Tucks`, which is stronger: it covers events, starts included |
| `joinedPlaced` (`Fmt/PlaceProofs.sw:301`) | same clause, for any `Doc` | yes | `printedWords` |
| `printedJoins` (`Doc/Joins.sw:1082`) | `wordsOf printed = doc.words` becomes `Every holds …` | yes, for a doc with `Closing` after a `LineSuffix` | `printedWords` (`:1118`) gives order exactly for any filter that drops closers or drops comments. Together they fix everything but the relative order of a closer and a comment, which is what rule N changes. `printedWordsExample` shows the hypotheses can be met |
| `readingWords` (`Doc/Words.sw:976`) | equality becomes filtered equality, with `Marked` and `apart` | yes | `Marked` ties every `Closing` leaf to `closer` and every `LineSuffix` to `suffix`. It doesn't constrain `Chunk`s, which only makes a filter drop more, and is sound |
| `stepWords` (`Doc/Words.sw:415`) | right side is `cmd.wordsFrom printer …` | yes: a `Closing` step writes before the waiting suffixes | `Doc.wordsFrom` says exactly that |
| `printLays` (`Doc/Lays.sw:860`) | gives `∃ laid, spec place laid ∧ Tucks laid printed` | yes | `Tucks` (below) |
| `printedEvents` (`Fmt/EventProofs.sw:2996`) | `FileEvents file printed` becomes `∃ laid, FileEvents file laid ∧ Tucks laid printed` | yes | the strongest true form: the laid trace is the file's and the printed one differs only by tucking |
| `printedPlaced` (`Fmt/DirectProofs.sw:29`) | adds `laid` and `Tucks`; views are the printed trace's | yes | `settledViews` (`:59`) gives the views of the file's events after rule N, as the proposal's §3.1 states it (trailing-comma hypothesis absent because the toy parses none yet) |
| `lexFits` (`Fmt/CarryLex.sw:257`) | `Parse.Fits` becomes `Tidy ∧ Rising` | content unchanged; see finding 2 | `settledFits` |
| `parseReads` (`Syntax/BlockProofs.sw:861`) | reads `lexed.settled` | follows `parse` | |
| `closerPasses`, `closeAfterPasses`, `closeAfterRule`, `writesCloseAfter` | narrowed to a token, or to a closer with own-line comments | follow `closer`'s and `closeAfter`'s new signatures; the bare case is `bareCloser`'s (`Closing`), covered by `closingPasses` and `closingRule` | |
| removed: `looseFree`, `looseMeets` | | false once `Meets` and `Free` say something at `Waiting` | `Gapped` |
| removed: `BareLast…`, `withCommas…`, `FineStep`, `stepComments`, `lexicalWithCommas`, `parametersBare` | | commas hold nothing | |
| removed: `readingLays`, `stepLays`, `printsLay`, `fillSepsLay`, `optionLays`, `headOrLays`, `printLaysExample` | | renamed to `…Puts` in `Places.sw` (printed order) and restated in `Lays.sw` (laid order) | |

Nothing the top theorems relied on is now unguaranteed: they are all
proved, with no axioms and no open goals.

### 2. Route (A), `Comments.closing`, is sound

- **No comment lost, order kept:** `closingAll`: `(close.closing
  before).all = close.all`. It fires only when `above` is empty, so
  `[comment]` above with nothing after has the same list.
- **A defined place:** above the closer, as an own-line comment.
  `closingSettled` holds for every input, and a closer with a comment
  above it is never moved by rule N (`movesPast` needs no own-line
  comment above), so the place is stable under print and re-parse. Because
  `printParses` is proved for every `Parsed` tree, a tree where it fired
  would still round-trip.
- **`closingSame`:** on a settled closer it is the identity. The
  read-back needs this.
- **Unproved:** that it never fires on settled tokens (finding 3). I
  looked for a mismatch between the tree's `before`
  (`endsWithComment`, `itemsEndWithComment`, `groupsEndWithComment`) and
  rule N's token-level "the previous token has a trailing comment". The
  one structural place it could differ is `statementsEndWithComment`
  returning `False` for a final `StatementNote` in an `if` branch inside
  brackets, but own-line comments before a closer go to the closer's
  `above` (probed). Twelve probes, none fired: `(if … else 2 -- note) -- d`
  with the note on its own line, the same with the note trailing,
  `[1 -- x, 2] -- d` (rule N moves `-- d` to `2`), `(-(x) -- x) -- d`
  (`-- d` stays on the inner `)`, `settledCloser` by `before`), and
  `fn f(a -- x) = 1 -- d`, among others. Trailing commas and `let` in
  brackets don't parse in the toy today.
- **Compared with T0's `receive`:** both move a comment that rule N would
  have moved somewhere well-defined, and neither is proved unreachable.
  `closing` is local (no recursion into the tree), which is why it cost
  about 40 fewer lemmas. Using it was a sound call.

### 3. The top theorems still mean what §3 says

`printParses`, `formatAnswers`, `formatRoundTrip`, `formatIdempotent`,
`formatSameTree`, `formatRefuses`, `formatRefusesOnly`, `parseCarries`
and `formatKeepsComments` are textually unchanged. (There is no
`formatAgrees`. The brief's list predates `formatSameTree`.) Their
meaning moved with `parse`, which now settles, and with `Parsed`, which is
stronger (finding 5). `parseParsed` is proved for every parse result, so
no hypothesis was added that narrows them to trees the parser doesn't
produce.

- **Same program:** `formatRoundTrip`: the output parses to the source's
  tree, the tree after rule N. A comment that rule N moves (`f(x) -- d`
  is `x`'s comment) is part of that tree on both sides.
- **No comment lost:** `formatKeepsComments` compares the lexer's
  comments of the source and the output, in order, without going through
  the tree. With `parseCarries` going through `settledKeepsComments`,
  rule N is inside the proof. So SKETCH-PLUS's D candidate 1 ("a rule N
  that drops a comment satisfies all three") is closed: Rust's
  finding-1 bug would fail this theorem.

### 4. `Tucks`, `Settled` and `settle`

- **`Tucks` (`Doc/Lays.sw:407`) says what its doc claims.** The two traces
  split into the same stretches. A stretch is either one event or a
  trailing comment (`IsComment`, mid-line) followed by closers (`)`, `]`
  or `,`, mid-line) that come after it in the laid trace and before it in
  the printed one. `LineEnded` makes the stretch after a tucked one start
  a line. It can't hide reordering beyond that: the closers are contiguous
  after the comment in `laid`, and nothing else moves.
- **`Settled` is not a separate predicate.** It is `settledCloser before
  close` (`Syntax/Ends.sw:70`), a conjunct of `Shaped`
  (`Syntax/ExpressionProofs.sw:309`), `ShapedType` and `ShapedParameters`
  (`Syntax/ShapeProofs.sw:235`, `:249`) and `ParsedHeader`
  (`Fmt/WalkProofs.sw:731`). Its doc matches rule N's stop conditions
  (`movesPast`, `Settle.sw`): an own-line comment above the closer, or a
  trailing comment on the token before. The `before` functions cover the
  opening bracket of an empty list, call or parameter list, as SKETCH-PLUS
  said they must. The printer side uses it through `calm`
  (`Fmt/CalmProofs.sw`), which is rule N's normal form on events.
- **`settle` is total:** `homed` recurses on `earlier`, `carryForward` on
  `tokens`, and `Lexed.settled` folds. Nothing uses fuel or is marked
  partial.
- **`settle` preserves comments:** `settledKeepsComments`
  (`Syntax/SettleProofs.sw:129`) says the same comments in the same order.
  `settledBare` and `settledOffsets` say only comments move, and
  `settledLexemes` says the lexemes are untouched. Idempotence is open
  (finding 4).
