# Where printed comments and blank lines stand (SW-4042)

Fable, 18 November 2026. Paper, with `stitchwort check` of one namespace
and one probe run through it. Ticket E of
`docs/reviews/SW-4025-output-statements.md` (§4). The statement is in
`tools/fmt/src/Fmt/TriviaStatements.sw` (namespace
`Fmt.TriviaStatements`): one open goal, `printedStands1`, and five
theorems proved by computing.

How claims are marked: **[checked]** `stitchwort check` accepted it;
**[computed]** a `byComputing` theorem or the probe gave it; **[source]**
read in the code, place given; **[inferred]** my reasoning.

## In plain words

**The problem.** Formatting twice must change nothing. The second run's
rule N moves comments by reading three things of each token: whether it
starts its line, the comments above it, and the comment after it.
Nothing proved says what those are for a printed file. `printedSpells`
gives the texts in order and `hangs` the columns; neither says which
token the lexer hands a comment to.

**The change.** One statement, `printedStands1`, as a test (`stands`)
that walks a declaration's printed leaves against the tree's words. It
needs no new idea about the rules: the printer writes each comment next
to its word, then lets closers and commas slip in front of a trailing
comment on the same line. `stands` says exactly that.

**What it should do.** `printedSettle1` (ticket G) follows from it with
two lemmas that exist (`chainSteps`, `landedHere`) doing the work on rule
1. The proof of `printedStands1` itself (ticket F) should be four lanes,
not the five that `printedHangs` took, because no columns enter and it
can follow the shape of `printedSpells` [inferred]. No slice is narrowed
and no end theorem is weaker: there is no D question.

## 1. The statement

`leaves` are `decl.leaves1`, what the declaration's printed text lexes to
alone. `words` are `decl.stood`: `decl.calm.words` (commas left out, as
the tree has none) with the `def`'s own-line comments and blank line
taken off, since the file loop prints those.

```stitchwort
def stands (owed: Option Text) (words: List Word) (leaves: List Leaf): Bool

theorem printedStands1 ∀ (decl: Decl)
    (within: decl.within1 = True) (shaped: decl.shaped1 = True)
    (settled: decl.settled1 = True) (lexical: decl.lexical1 = True):
    stands None decl.stood decl.leaves1 = True
```

`owed` is the trailing comment of a word already passed which the lexer
has not seen yet. `stands` says, leaf by leaf:

1. **Own-line comments and blank lines.** Every leaf but a comma is the
   next word: its text, the word's own-line comments above it in order,
   each with its blank-line flag, and the word's own blank-line flag.
   The flags are `calm`'s exactly: a blank line is printed where the
   rules read the flag and nowhere else. A comma has no comment above it
   and no blank line.
2. **A trailing comment** is on its word's leaf, or it is owed on. While
   one is owed, every leaf is a comma, or a closer whose word has no
   comment after it; none of them starts a line; and the first that
   holds a comment holds the one owed. So the comment is on the last of
   the closers and commas that follow its word on its line, which is
   where the lexer puts it.
3. **A closer whose word has a comment after it starts its line.**
4. Nothing else holds a comment, and at the end nothing is owed.

Why this form:

- **It is in rule N's terms.** Rule 1 reads `lineStart`, `leading` and
  `trailing`, and walks back past commas and closers that don't start a
  line (`stepsBack`). Clause 2 is `chainTo` of `SettleProofs.sw:1983`
  read forwards; clause 3 is the first half of `stopsAt`.
- **It is a test**, so every claim below was run.
- **It is a fold with one piece of state**, so it joins across
  declarations (`stands None` of two lists gives `stands None` of their
  append) and G is one induction.
- **It doesn't mention columns**, nor `hangs`.

What it leaves to G, on purpose: the second half of `stopsAt` (the
closer has own-line comments, or the code before it ends with a
comment). That is `homedBack` of the tree, which `settled1` gives; it is
a fact of the words, not of the printing.

## 2. Witnesses and the probe

All in `Fmt.TriviaStatements` [checked: the namespace checks, 8 goals
open, of which 1 is new and 7 are `OutputStatements`'].

| Theorem | What it shows |
|---|---|
| `standsOnExample` | `holdsOnExample`'s source: comments above declarations, after an opener, a comma, a `->`, a closer; a blank line above an item's comment |
| `standsOnClosers` | closers that hold comments: after an item ending with one, under own-line comments, and `[(a -- x⏎)⏎] -- c`, where `)` goes on `a`'s line and `]` takes its own |
| `standsOnTucked` | `g ((a -- c⏎), b)`: the comment is owed past `)` and the comma |
| `unsettledFalls` | **`settled1` is needed.** `(b) -- c` as a hand-built tree has every other hypothesis; the `)` stays on `b`'s line, starts none, and clause 3 fails |
| `unsettledStands` | **`stands` alone is not enough for G.** `[a -- x⏎, b] -- c` (SW-4025's `unsettledFile`) stands, because its list breaks and the `]` starts a line; yet rule N takes the comment back to `b`. G reads `settled1` again, for where rule 1 stops |

**Probe** [computed; `stitchwort run`, a scratch namespace, since
deleted; generator and results in the lane's scratch folder]. Three
token rows (`def d : A -> B := g [ a , ( b ) , c ] ( x , y ) z`, one
with nested brackets and operators, one with a tuple type), each
re-laid with a comment after every token, a comment above, a blank
line, a blank line and comment, and every pair of those within three
tokens of each other: 699 sources.

- 699 of 699 have the four hypotheses and `hung1`, **stand**, and give
  `printedSettle1`'s conclusion.
- 238 have a comment on a comma or closer that doesn't start its line
  (clause 2 at work); 6 a closer holding a comment at a line start
  (clause 3); 86 a blank line in the output; 307 an own-line comment
  inside a declaration.
- A first generator laid closers at the items' column; 21 of its 416
  sources didn't parse and 4 fell outside the slice. The other 391
  stood. Nothing was found against the statement.

Not covered: widths other than the formatter's (the theorem is at
`width`, as `leaves1` is), and trees no parse gives other than the two
unsettled ones.

## 3. How the printer makes it true [source]

- A word is written by `Word.leaf` (`Rules.sw:145`): its `leading` (the
  own-line comments, each on a line, and a `Blank`), the text, its
  `trailing` comment. So in the order the document has them, each
  comment is beside its own word.
- A closer or comma is a `Closing` (`Rules.sw:101`), which the engine
  writes in front of a comment waiting on the line. `Std.Doc`'s `Tucks`
  says so of the printed trace against the laid one: a `Tucked` stretch
  is a comment that starts no line and `Closer`s that start none
  (`Stretch.Fits`), and the next stretch starts a line (`LineEnded`).
- A closer that holds a comment and has none above it gets
  `CloserLine`, a line of its own, exactly when `around.before`
  (`Word.leaf`'s `ownLine`), which for a bracket's closer is
  `trailsBeforeClose`, `homedBack`'s `trailsBack`. With comments above
  it, it starts a line anyway.

So the proof has three parts that don't mix: the document's own order
(the rules), the tuck (the engine, proved), and the lexer's reading (as
`tracks` did for columns).

## 4. Ticket F: proving `printedStands1`

**The route** [inferred]. Follow `printedSpells`, not `printedHangs`.
`Spells doc texts` is `Uniform doc ∧ Marked … ∧ doc.words = texts`
(`SpellProofs.sw:34`): a function on the document, with one `Std.Doc`
theorem (`printedWords`) taking it to the printed text. The rules' side
is then rewriting, which is why it was Sonnet's. `printedHangs` instead
proved a `Lays` triple per rule, with every side condition of `Lays`
re-established, because columns depend on the layout chosen. Whether a
comment starts a line does not: after a word's text the line is begun
whatever the layout, and `LineStart` begins a line whatever it was.

So: a function `Doc.told` giving the document's *reading*, a list of
entries (a word with its comments and flags, and whether it is known to
start a line), computed with one bit of state (is the line begun: yes,
no, or either). The reading rule is the lexer's:

- a comment met where the line is begun is the last entry's `after`;
- a comment met at a line's start, and a `Blank`, wait for the next
  entry;
- a `Line`, `SoftLine` or fill separator leaves the bit at "either"; a
  comment met at "either" has no reading (the rules never do it, and
  the walk shows it by getting a value).

| Lane | What | Model | Est. |
|---|---|---|---|
| F1 | `Std.Doc.Proofs`: `Doc.told`, and `laysTold`: every trace a `Uniform` document `Lays` reads as `doc.told` (one induction over `Doc`, as `MarkProofs.framed`); each `CloserLine` closer's event starts a line | Opus | 45 min |
| F2 | `Fmt/ToldProofs.sw`: the words. `Word.leading`, `Word.leaf` (four closer cases), `Word.opening`, `closerNotes`: each one's `told` is its word, flags as `Comments.kept`; then atoms, parens, prefix | Sonnet | 35 min |
| F3 | The rest of the walk: `commaBracket` in its three layouts and the hug, `appDocs`, chains, `defDoc`, `doc1`: `doc.told` is `decl.stood` with a bare comma entry between items, and each closer whose word trails is marked as starting a line (from `settled1`: `homedBack` to `around.before`, with `trailsBackAppend`) | Sonnet | 45 min |
| F4 | The engine end, in `Fmt/PrintHangProofs.sw`'s manner: the tuck (`Tucks` turns a laid reading into `stands` of the printed one, by induction over stretches); `Laid.lay` reads the printed events as the fold does (`tracks` with one more conjunct); then `printedStands1` as `printedHangs` is assembled | Opus | 50 min |

- **Order.** F1 first: F2 and F3 need `Doc.told`. F4 needs only F1's
  statement, so it runs beside F2. F2 then F3.
- **Models, by D3682.** F2 and F3 are walks over the rules with the
  statement fixed. F1 chooses a definition others build on, and F4 has
  the invariant (what is owed across a stretch).
- **Files.** New ones, so nothing clashes with SW-4045 (the hang
  proofs) or SW-4039 (`OutputStatements`). F4 imports
  `PrintHangProofs` and doesn't edit it.
- **What F4 reuses.** `printLays` and `Tucks` (`Std.Doc.Proofs`);
  `tracks`' induction over the printed texts, `pieceFoldLay`,
  `laidOfFold`, `pairsEnd` (no text follows a comment on its line);
  `printedLexes`' hypotheses from `doc1Spells`, `doc1Passes`,
  `declJoins`, `declPrintable`, exactly as `printedHangs`' last six
  lines pass them. It needs a `Lays` of the document to feed
  `printLays`; `doc1Hangs` gives one, from `DeclHangs`.
- **So `printedStands1` gains a hypothesis until SW-4045 lands**:
  `DeclHangs lexKind decl`, as `printedHangs` has. It goes when
  `DeclHangs` is derived. The orchestrator's call, not a weakening of
  the end theorem.
- **If F1 finds `Lays` won't give the reading without the places**
  (say a comment's event needs the exact `Place`), the fallback is the
  `HangLays` shape with the reading as the fold: about 40 combinator
  lemmas copied, then the same walk with seats. Two more Opus lanes.
  F1 reports before starting it.

**Where the blank lines come from.** `stands` asks the flags to be
`calm`'s. `calmPrints` says the calm tree prints the same; F2 states
each word's reading for a calm word, where every flag left is one the
rules print a `Blank` for. The cases are `Comments.kept`'s (`item`,
`closer`) [source: `Predicates1.sw:63`].

## 5. Ticket G: `printedSettle1` from `printedStands1`

One Opus lane, 45 min, taking `SourceFile.stood1` as a hypothesis so it
can run beside F.

1. **The file stands.** `standsAppend`: `stands None` joins. With
   `headed` putting the file loop's comments on each `def`
   (`laidNotes`, `Decl.laid1`), the file's leaves stand against all the
   declarations' `calmTop` words in a row.
2. **Rule 1** (`homeStands`, the one real induction). Over `homeFrom
   behind None rest` with `stands owed words rest`. The invariant on
   `behind`: its commas are bare; its words are the words done, but
   that when a comment is owed the word that owes it is `steps` back,
   lacks it, and `chainTo steps behind` holds.
   - A comma or closer that passes the comment on: nothing moves.
   - The leaf that holds an owed comment: `chainSteps` gives `stepsBack
     = steps` and `trailingAt` puts it on its word.
   - A word holding its own comment: no closer, or `landedHere` with
     `stopsAt`: the line start is clause 3; "comments above or the line
     before ends with one" is `homedBack` through a lemma `endsOn
     behind = trailsBack` of the words done.
   - Under the alphabet, `movableQuiet1`, `skippedQuiet1`,
     `barsQuiet1` and `endsOnQuiet1` remove bars; `walkLands` isn't
     needed.
3. **Rules 2 to 5 are idle** on the result, as in `settledIdempotent`'s
   proof: `commasIdle` (bare commas), `arrowsIdleAll` (the tree's
   `arrowsBare`, read off the leaves' words), `letsQuiet1`, and
   trimming a `commentText` is no change.
4. **Groups.** `settledKeepsTokens` and `printedGroups1` cut the
   settled leaves as the declarations; `groupWordsConcat`,
   `groupsConcat` and `declsSettled` (`SettleSplitProofs.sw`) take the
   one list back to a list per declaration. The end's comments pass
   rule 2 with nothing carried.

- **From `printedHangs`:** only `hung1`, for the groups, as before.
- **From `hangsOfLays`:** nothing in G. F4 reuses its parts (§4).
- G's estimate stands at SW-4025's 45 min: the walk it feared is
  `chainSteps`, already proved for K1's `laidFrom`.

## 6. Decisions

**No D question.** The slice is not narrowed and neither end theorem
changes. SW-4025's D question (b), "the same program" first, is
untouched.

Orchestrator's calls:

- `printedStands1` carries `DeclHangs` until SW-4045 removes it (§4).
- F as four lanes, 2 Opus and 2 Sonnet, about 3 hours of agent time in
  all; SW-4025 guessed two or three Opus lanes at 45 min.
- A new file for the statement, to keep clear of SW-4039.

## 7. Findings

- `SettleProofs.sw:1880` on (`laidFrom`, `relaid`, `relayFrom`,
  `chainTo`, `chainSteps`) is half of K1's `settledAnyLayout`; nothing
  uses it yet. G is its first user. If G lands, the unused half
  (`laidFrom`, `relayFrom`, `laidFromOnto`) can go.
- The lexer's layout fact `laidOut` for printed leaves comes free from
  `lexLaid1` and `printedFileLexes1`; G doesn't need it, since `stands`
  carries the line starts it reads.
