# What slice 1 must still say about the output (SW-4025)

Fable, 18 November 2026. Paper, with `stitchwort check` of one namespace
and probes run through it. The statements are in
`tools/fmt/src/Fmt/OutputStatements.sw` (namespace
`Fmt.OutputStatements`): seven open goals, which check, and six theorems
proved by computing. It follows `docs/reviews/SW-4018-parser-statements.md`,
whose §5.4 and §5.5 it settles (and partly corrects).

How claims are marked: **[checked]** `stitchwort check` accepted it;
**[computed]** a `byComputing` theorem or a probe run in that namespace
gave it; **[source]** read in the code, place given; **[inferred]** my
reasoning.

## In plain words

**The problem.** Formatting twice must change nothing. The second run
lexes the first run's output, runs rule N on it and parses it. Nothing
proved yet says what those three steps give for a printed file. The plan
named two theorems for it, `printedKeeping` ("rule N does nothing to the
output") and `printedSettle1`, and left the file level to glue.

**The change.** I wrote the output's leaves down exactly, ran every
candidate statement on 33 formatted files and three hand-built trees, and
kept the ones that hold.

**What it should do.**

- **`printedKeeping` is false as planned, and is replaced.** Rule N is
  not idle on the output: in `(a, b) -- c` the lexer gives the comment to
  `)`, and rule N takes it back to `b`. The same after `a,`. 4 of the
  first 16 probes [computed: `outputNotIdle`]. What holds is that rule N
  puts every comment back on the token the tree has it on: that is
  `printedSettle1`, now the one statement of item 4.
- **Read-back's planned end, `read.calm = T.calm`, is false** of a
  source that starts with a blank line [computed: `topFlagLost`]. `calm`
  keeps the flag on the file's first `def` or comment, the file loop
  never prints that blank line, so the output's tree has no flag. A
  one-flag fix to `calm` (`calmTop` here) makes the output's parse equal
  to it word for word on every probe.
- **The file level is one exact equation**, `lex file.printed1 = Ok
  file.lexed1`, with the alphabet, no last comma, `plain1` and the
  parser's groups as four corollaries.
- **One piece is missing that no ticket covers:** where the printed
  text puts each comment (its own line, or the end of whose line) and
  each blank line. `printedSpells` is about texts in order, and `hangs`
  skips comments. Idempotence needs it; "the same program" does not have
  to. §4 and the D question.

## 1. The output's leaves

Write `T` for the tidied tree the driver prints, `out = T.printed1` and
`O` for what `lex out` gives.

```stitchwort
def laidOf (doc: Doc): Laid := (pieceFold lexKind (printedPieces doc width)).foldLeft Laid.start Laid.lay

def Decl.leaves1 (decl: Decl): List Leaf := match decl.doc1 with
  | Some doc => (laidOf doc).leaves.reverse
  | None => []

def SourceFile.lexed1 (file: SourceFile): Lexed := {
  leaves = (groupsFrom True file.decls).concat,
  end = { leading = laidNotes file.decls.isEmpty file.end.above, blankLines = 0, trailing = None }
}
```

- `Decl.leaves1` is `printLexes1Tree`'s right-hand side at the
  formatter's width, so `printedHangs` (SW-4034) is `hangs decl.leaves1`.
  `SourceFile.hung1` says it of every declaration; it is the form the
  statements below take it in.
- `groupsFrom` gives each declaration its leaves with the `def` holding
  the declaration's own-line comments (`laidNotes`: column 0, one blank
  line or none) and its blank line (`Decl.laid1`, `headed`). The first
  thing in the file gets no blank line whatever its flag says, as
  `Output.item` prints none [source: `Slice1.sw`, `Output.item`].
- A `Token` has no offset or line number, only its column and whether
  it starts its line [source: `Token.sw:309`], so a declaration's leaves
  in the file are its leaves lexed alone, but for the first one's
  comments. That is why the equation can be exact.

## 2. The statements

Every statement takes `T`'s facts in the forms the merged theorems give:
`within1`, `shaped1`, `settled1`, `lexical1` (the four `printLexes1Settled`
takes), and `hung1` where a line start matters. None takes `commaFree`:
the rules never print a last comma, whatever the tree's flag says
[source: `SpellProofs.sw:484`, `commaSpelt` ignores the flag].

`holdsOn source` in the file runs every hypothesis and every conclusion
on a source's tidied tree, then the output's parse. It is true of three
`byComputing` witnesses [checked] and of 30 more sources run as a probe
[computed]: comments above declarations, at the end, after openers,
commas, closers, operators and `def`; closers holding comments in each of
`homedBack`'s cases; blank lines in every place the parser sets a flag; a
file of comments only; the empty file; a 200-column call.

### 2.1 `printedTokens1` (one declaration; the bridge from texts to leaves)

```stitchwort
theorem printedTokens1 ∀ (decl: Decl) (within …) (shaped …) (settled …) (lexical …):
    tokenTexts decl.leaves1 = decl.spelt.filter notComment ∧ decl.leaves1.all Leaf.kinded = True
```

- **Why.** `printedSpells` speaks of the printed texts; read-back, the
  alphabet, `noLast` and `plain1` all need the same of the leaves. This
  is its second half (the texts without comments, commas included)
  carried across `laidOf`, with each leaf's kind the lexer's for its text.
- `printedSpellsSettled` also takes `Decl.real` (no word's text is
  layout). It follows from `lexical1` [inferred: a text that lexes as one
  token isn't spaces or a line break]; the lane proves that or reports.

### 2.2 `printedFileLexes1` (item 5: the text lexes)

```stitchwort
theorem printedFileLexes1 ∀ (file: SourceFile) (within …) (shaped …) (settled …) (lexical …):
    lex file.printed1 = Ok file.lexed1
```

- Exact, columns and blank-line counts included [computed on all 33].
- **What the printer side supplies:** `printLexes1Settled` per
  declaration; `settled1` for the notes' texts (`commentText`, through
  `Decl.words`' `def` and `file.end`).
- **What it does not yet supply** [inferred]: that a declaration's
  printed text ends with a token or its trailing comment (no line break
  last, nothing waiting), and that the pieces may follow one another
  across the file loop's line breaks. Both are in the lane.

### 2.3 `printedAlphabet1`, `printedNoLast1` (item 5), `printedPlain1` (item 4), `printedGroups1`

```stitchwort
theorem printedAlphabet1 …: alphabet1 file.lexed1.leaves = True
theorem printedNoLast1 …: noLast [] file.lexed1.leaves = True
theorem printedPlain1 … (hung: file.hung1 = True): plain1 (tokens file.lexed1.leaves) = True
theorem printedGroups1 … (hung: file.hung1 = True): groupsOf file.lexed1.leaves = groupsFrom True file.decls
```

- All four follow from `printedTokens1`'s token order and kinds.
- `printedPlain1` needs `hangs` for one clause only: no comma starts a
  line. `printedGroups1` needs it for "a later leaf that starts a line is
  right of column 0, unless a closer or `:=`".
- `printedGroups1` was in nobody's list: the parser reads a group at a
  time (`parseGroups`), read-back is proved a group at a time
  (`readsBackLine`), and nothing said the output's groups are the
  declarations.
- `printedNoLast1` gives `O.settledOnce = O.settled` by `settledOnceNone`.

### 2.4 `printedSettle1` (item 4: rule N on the output)

```stitchwort
theorem printedSettle1 ∀ (file: SourceFile) (within …) (shaped …) (settled …) (lexical …)
    (hung: file.hung1 = True):
    (groupsOf file.lexed1.settled.leaves).map codeWords = file.calmTop.decls.map Decl.words
      ∧ file.lexed1.settled.end.comments = file.calmTop.end
```

- **It replaces both planned statements.** "Settled leaves stay put" is
  false of `O` (`outputNotIdle`). "Printed leaves are homed, from
  `T.settled1`" is true of `O.settled` for free (`settledHomed`), and
  says nothing about which token holds a comment. The fact the second
  run needs is this one: after rule N, the leaves' words are the tree's.
- **`settled1` is what makes it true, and is needed** [computed:
  `settledNeeded`]: a hand-built tree with every other hypothesis, whose
  `]` holds a comment rule N would have moved, prints with the comment
  on `b`'s line; the conclusion fails.
- **Exact, flags included.** The right-hand side is `calmTop`, not some
  tree with the same `calm`: on every probe a blank-line flag comes back
  exactly where the rules read one. If a lane finds a blank line the
  printer adds where `calm` clears the flag (the sketch's family C, which
  no longer shows [computed]), the fallback is "some `twin` with
  `twin.calmTop = file.calmTop` whose words these are"; report it first.
- **`hung1`** is used only to cut the leaves into groups.
- A general "leaves that are homed, bare and trimmed settle to
  themselves" is true [inferred: `settledIdempotent`'s proof with its
  three facts as hypotheses] and is not stated: nothing on the path uses
  it.

### 2.5 `calmTop`

```stitchwort
def SourceFile.calmTop (file: SourceFile): SourceFile  -- calm, and the file's first flag cleared
```

`Header.calm` keeps the `def`'s flags "the file loop reads them all"
[source: `Predicates1.sw:99`, `Header.calm`]. It reads all but the first in the file.
Recommended: clear that flag in `SourceFile.calm` itself and re-prove its
four theorems (`calmTwice`, `calmWithin`, `calmMeans`, `calmPrints`);
`calmTop` then goes. Until then the statements use `calmTop`.

## 3. The final assembly, in outline

`L = lex source`, `T0 = parseFile L.settledOnce`, `T` its tidied tree.
Glue (SW-3973) defines the driver `formatWithin1`: lex, refuse outside
the alphabet, refuse a source that isn't `plain1` (the call on SW-4018's
D-B), parse and tidy, refuse outside `within1`, print.

**The tree's facts** (both theorems):

| Fact of `T` | From | State |
|---|---|---|
| `within1` | the driver's test, `commaKeepsWithin` | proved |
| `shaped1`, `lexical1` | `parseShaped1`, `parseLexical1`, `commaKeeps…` | proved, under `good` (SW-4024, running) and `frame` (SW-4017, backlog) |
| `settled1` | `lexLaid1` (SW-4023, running), `onceWordsSettled1`, `parseSettled1`, `commaKeepsSettled` | proved but `lexLaid1` |
| `commaFree` | `commaBare` | proved |
| `hung1` | `printedHangs` through `printLexes1Tree` | SW-4034, running |

**The output's parse** (both theorems): `parseFile O.settledOnce = Ok
T.calmTop`.

1. `lex out = Ok T.lexed1`: `printedFileLexes1`.
2. `settledOnce` is `settled`: `printedNoLast1`, `settledOnceNone`.
3. The settled groups' words are `T.calmTop`'s: `printedSettle1`.
4. Their tokens are the rules' spelling, commas between items, kinds the
   lexer's: `printedTokens1`, `printedGroups1`, `settledKeepsTokens`.
5. Each group hangs: `hung1`; `hangs` and `groupsOf` read only tokens,
   which rule N and `headed` keep (two small lemmas, glue's).
6. Read-back in file form (SW-4031, backlog): groups whose tokens and
   words are a tree's, each hanging, parse to that tree. `readsBackLine`
   is the one-line case. It needs `within1`, `shaped1`, `lexical1` and
   `commaFree` of `T.calmTop` (small lemmas across `calm`), and
   `fileRefusal` passing (the first leaf is a `def` in column 0).

**The same program.** `after = T.calmTop`; `calmMeans` (with the top
flag) and `tidyKeepsMeaning` give `after.meaning = T0.meaning`.

**Idempotence.** The second run: lexes (1); passes the alphabet
(`printedAlphabet1`); is `plain1` (`printedPlain1`); parses to `T.calmTop`
(1 to 6); P1, P3 and P4 change nothing (`forallSame1`, `bracketsSame1`,
`mergeSame1`), P2 nothing on a `commaFree` tree (small lemma, not stated
anywhere); is `within1` (`calmWithin`); prints `T.calmTop.printed1 =
T.printed1` (`calmPrints`, with the top flag).

**Still missing**, beyond the running lanes:

- **The printed comments' lines and blank lines** (§4): `printedSettle1`
  can't be proved from what the printer side has.
- **Read-back in file form** (SW-4031), with the interface of step 6.
- **`calm`'s top flag** (§2.5).
- **`formatWithin1`**, and glue's small lemmas named above.

## 4. The missing piece: where printed comments and blank lines stand

`printedSettle1` needs, of one declaration's printed leaves, three things
no theorem says [source: `SpellProofs.sw`, `PrintHangProofs.sw`,
`HangProofs.sw` read for it]:

1. each token's own-line comments are its word's, on lines of their own
   above it, and it has a blank line above exactly where `calm` keeps the
   flag; a comma has none;
2. a word's trailing comment ends the word's line, on the last token of
   that line: the word, or a closer or comma after it;
3. a closer that holds a trailing comment in the tree starts its line.

Given these and `settled1`, rule 1's walk (`stepsBack`, `walkLands`)
takes each comment from the last token of its line back to its word,
stopping on a closer exactly where `homedBack` lets the tree's closer
hold one; rules 2 to 4 find nothing; rule 5 trims nothing [inferred;
true on every probe].

- `printedSpells` gives the texts in order, in two filtered halves,
  because a closer and a trailing comment may swap. It has no line
  breaks.
- `hangs` and its trace fold skip comments and blank lines.
- So it is a third walk of the rules, with a fold over the trace that
  builds trivia as `Laid.lay` does. The frame is `HangLays`'; the
  columns, which made `printedHangs` long, don't enter.

Its statement should be written once SW-4034 has merged, in that
framework's terms, and checked against `holdsOn`'s sources: ticket E.

## 5. Tickets

Estimates are agent time. Today's proof lanes ran 10 to 50 minutes; the
`printedHangs` walk has taken four Opus lanes so far.

| # | Ticket | Model | Est. | After |
|---|---|---|---|---|
| A | `printedTokens1`: one leaf a `Code` piece, from `printedSpellsSettled`; `Decl.real` from `lexical1` | Sonnet | 25 min | now |
| B | `printedFileLexes1`: the file's text as pieces; `Laid.lay` from the state after a line break; a declaration's text ends with a token or its comment | Opus | 45 min | now |
| C | `printedAlphabet1`, `printedNoLast1`, `printedPlain1`, `printedGroups1` from `printedTokens1` | Sonnet | 40 min | A |
| D | `calm` clears the file's first flag; re-prove `calmTwice`, `calmWithin`, `calmMeans`, `calmPrints`; `calmTop` goes | Sonnet | 20 min | now |
| E | Paper: state the printed trivia fact (§4) as a test and an open goal, with witnesses | Fable | 30 min | SW-4034 |
| F | Prove E's statement: the trivia walk over the rules | Opus, two or three lanes | 45 min each | E |
| G | `printedSettle1` from E's statement, taken as a hypothesis: rule 1 lands, rules 2 to 5 idle | Opus | 45 min | E |
| H | SW-4031 (exists): read-back in file form, to §3 step 6's interface | Opus | as ticketed | SW-4034 |
| I | SW-3973 (exists): `formatWithin1`, the small lemmas, the two end theorems | Opus | 40 min | all |
| J | SW-4003 (exists): the checkpoint review | Fable | 30 min | I |

A, B and D touch no file a running lane touches. B is Opus for the seam
between declarations; A, C and D are walks over lists.

## 6. Decision

**D question (Matt, scope and order): idempotence needs a walk nobody
planned.** Tickets E to G are three to five lanes that the plan had
folded into "`Spells`, with their comments".

- **(a)** Both end theorems wait for it. Read-back is stated for the
  tree `T.calmTop` itself.
- **(b)** "The same program" lands first, without it. Read-back is
  stated for any comments: groups whose tokens spell `T` parse to `T`
  with the leaves' comments (a relabelling of the tree, one lane more,
  and the more general theorem for later slices). `meaning` reads no
  comment, so the same program follows from tickets A to C and
  `printedHangs` alone. Idempotence follows when E to G do.

Recommendation: (b). The headline theorem stops depending on the
longest and least certain piece, and the extra lane isn't thrown away.
No slice is narrowed and neither end theorem is weakened either way.

Orchestrator's calls, not Matt's: `calmTop` (§2.5, an internal predicate
found false), and dropping `printedKeeping`.
