# What slice 1 must still say about the parser (SW-4018)

Fable, 18 November 2026. Paper, with `stitchwort check` of one namespace.
The statements are in `tools/fmt/src/Syntax/ParseSettledStatements.sw`
(namespace `Syntax.ParseSettledStatements`): four open goals, which check,
and five examples proved by computing.

How claims are marked: **[checked]** `stitchwort check` accepted it;
**[computed]** a `byComputing` example or probe in that namespace gave it;
**[source]** read in the code, place given; **[inferred]** my reasoning.

## In plain words

**The problem.** The two top theorems of slice 1 (formatting keeps the
program; formatting twice changes nothing) are put together by glue
(SW-3973) from each layer's theorems. The sketch names three parser
theorems nobody has stated: `parseSettled1`, `parseCarries1` and
`fuelEnough1`. A wrong or weak statement here would be proved happily and
found only when glue fails to close.

**The change.** I followed both top theorems through every merged layer
and wrote down what the parser has to supply, as statements that check.

**What it should do.**

- **One new parser fact is needed, `parseCarries1`:** a declaration's
  words are its tokens, commas left out. It is a second walk over the
  parser's slice 1 path, about 120 to 200 theorems [inferred].
- **`parseSettled1` needs no walk of its own.** It follows from
  `parseCarries1` by list reasoning, given that rule N's result is settled
  when read as words. That last part (`onceWordsSettled1`) is new and is
  rule N's, not the parser's.
- **`fuelEnough1` is not needed.** Read-back already proves the parser
  succeeds on printed text, fuel included; no top theorem needs more.
- **Five conditions have no lane.** The largest: nothing is proved about
  what the lexer gives for a *source* (only for printed text), and the
  parser theorems' `good` hypothesis is false of two kinds of token the
  slice admits, qualified names (`List.map`) and numbers with an exponent
  (`1e3`) [computed]. §5 lists them.

## 1. What glue needs, followed through

Write `L` for the lexed source, `S = L.settledOnce` for the leaves the
driver parses, `T0` for the parse, `T` for the tidied tree and `O` for the
lexed output.

**Keeps meaning.** `parse1 output = Ok after` with `after.calm = T.calm`
(read-back), then `calmMeans` twice and `tidyKeepsMeaning`. Read-back and
the rules need, of `T`: `within1` (the driver's test), `shaped1` and
`lexical1` (`parseShaped1`, `parseLexical1`, then `commaKeepsShaped`,
`commaKeepsLexical`), `commaFree` (`commaBare`), and `settled1`
(`commaKeepsSettled`, then **`parseSettled1` on `T0`**).

**Idempotence.** The output lexes to `O` (`printLexes1`), passes the
alphabet, `O.settledOnce = O.settled` (`settledOnceNone`), rule N moves
nothing in `O`, and `parseFile O = Ok read` with `read.calm = T.calm`
(read-back). Then P1, P3 and P4 change nothing (`forallSame1`,
`bracketsSame1`, `mergeSame1`, with `calmWithin`), P2 changes nothing
(`read` has no trailing comma, since `calm` doesn't touch that flag), and
`read.printed1 = read.calm.printed1 = T.calm.printed1 = T.printed1`
(`calmPrints` twice). **Nothing is needed from the parser about the second
parse** but what read-back gives: `lexical1` of `read`, which `calmPrints`
asks for, comes across `read.calm = T.calm` (`Word.keptLexesAs`).

So the parser owes exactly: `shaped1`, `lexical1` and `settled1` of the
source's parse. The first two are proved. `settled1` is a test on the
tree's words (`Decl.words`), and what is known is about leaves, so the
missing link is that the words are the leaves.

## 2. The statements

All four take the hypotheses in the forms the merged theorems give or
take. `holdsOn` in the file runs every statement's conclusion on a source;
it is true of a two-declaration file with comments in every kind of place,
of a last comma holding a comment, and of a comma starting a line
[computed]. Eleven more probes, deleted afterwards, found no exception:
comments around `->` and `→`, nested closers each with a comment, a
closer after an own-line comment, trailing spaces in comments, an
unparseable file with a closer in column 0.

### 2.1 `parseCarries1` (the parser's)

```stitchwort
def codeWords (leaves: List Leaf): List Word := leaves.filter (leaf => leaf.kind != Comma) |> .map Leaf.word

theorem parseCarries1 ∀ (frame: FrameRest expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: List.All (group => List.All GoodItem (items group)) (groupsOf lexed.leaves))
    (parses: parseFile lexed = Ok file)
    (within: file.within1 = True):
    file.decls.map Decl.words = (groupsOf lexed.leaves).map codeWords ∧ file.end = lexed.end.comments
```

- **Why this form.** An equality of words, comments included, per
  declaration. It is the strongest thing true: every weaker form (the
  texts only, or the comments only) would have to be proved again for
  `formatWithinKeepsComments`, which needs each comment on its token.
- **No "commas are bare" hypothesis.** The words are equal whether or not
  a comma held a comment; that a comma's comment isn't lost is rule N's
  `settledCommasBare`, used where comments are counted, not here.
- **`good` is needed** for `def`, `:` and `:=`: the tree keeps only their
  comments and `Decl.words` writes the texts back, so the leaf's text must
  be the kind's spelling.
- **`frame` as in `parseShaped1`**: a declaration that isn't a plain
  definition must be shown outside the slice. SW-4017 removes it from all
  three at once.
- **How to prove it** [inferred]. A `Parse.ReadsIn` walk with the spec
  `read value => value.within1 = True → value.words = codeWords of read`,
  one lemma per function on slice 1's path. Every `Parse.Gives … Out` fact
  in `ParseWalk` (the parsers outside the slice) gives its lemma by
  `Parse.readsWeaken`, since the spec is empty of a tree outside the slice;
  so the new work is the path from `expr` down to the atoms and the `def`
  frame, not the 23 outside facts.

### 2.2 `parseSettled1` (a corollary)

```stitchwort
def settledWords (words: List Word): Bool :=
  homedBack words.reverse && arrowsBare words && words.all (word => word.comments.texts.all commentText)

def Lexed.wordsSettled1 (lexed: Lexed): Bool :=
  settledWords (codeWords lexed.leaves)
    && lexed.end.comments.texts.all commentText
    && lexed.end.comments.after.isNone

theorem parseSettled1 ∀ (frame: FrameRest expressionAt) (lexed: Lexed) (file: SourceFile)
    (good: …) (parses: parseFile lexed = Ok file) (within: file.within1 = True)
    (settled: lexed.wordsSettled1 = True):
    file.settled1 = True
```

- `settledIsWords` (`decl.settled1 = settledWords decl.words`) is proved,
  by computing [checked].
- **The hypothesis is over the whole file's words, not a group at a
  time.** Rule N looks back for the code before a closer across the whole
  file. Per group the statement that rule N gives it would be false:
  `def a: A := b -- c⏎)⏎ ) -- d` (which doesn't parse) has a second group
  `) )` whose last closer is homed only by `b`'s comment in the first
  [inferred from `endsOn`; the whole-file form is true of it, computed].
  `parseSettled1` has `parses`, so it can cut the file's words at each
  `def`, which no look back passes.

### 2.3 `onceWordsSettled1` (rule N's) and `lexLaid1` (the lexer's)

```stitchwort
def Lexed.laid1 (lexed: Lexed): Bool :=
  laidOut False lexed.leaves && lexed.leaves.all Leaf.marked
    && (lexedTexts lexed).all rawComment && lexed.end.trailing.isNone

theorem lexLaid1 ∀ (source: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed) (within: alphabet1 lexed.leaves = True):
    lexed.laid1 = True

theorem onceWordsSettled1 ∀ (lexed: Lexed)
    (within: alphabet1 lexed.leaves = True)
    (plain: plain1 (tokens lexed.leaves) = True)
    (laid: lexed.laid1 = True):
    lexed.settledOnce.wordsSettled1 = True
```

- **Why `onceWordsSettled1` is needed at all.** Rule N's theorems
  (`settledHomed`, `settledArrowsBare1`, `settledTrimmed`) are about
  `lexed.settled`; the driver parses `lexed.settledOnce`, which is
  `settled` of other leaves. And they speak of leaves and kinds, where
  `settled1` speaks of words and texts. Two gaps, one statement.
- **`settledHomed` can't be used on `settledOnce` directly.**
  `withBareLastCommas` puts a last comma's trailing comment on the leaf
  before it and leaves the comma, bare, on the same line: a leaf after a
  trailing comment that doesn't start its line, which `laidOut` forbids
  [source: `Settle.sw`, `commaMoved`]. The way round is `bareSettles`:
  `settledOnce`'s leaves, last commas dropped, are `settledBare`'s, and
  the leaves `settledBare` settles (without last commas) are still laid
  out and `plain` [inferred; to be proved in this ticket].
- **`Leaf.marked`** says the text and the kind agree about closers and
  `->`, which is what turns `kind.isCloser` into `isCloserText`. It is
  true of every token the lexer gives, qualified names included, where
  `Spells` isn't (§5.1).
- **`plain1` is a real hypothesis**, not one a lane can remove: §5.3.

## 3. Verdicts on the three names

| Name | Verdict | Stated as |
|---|---|---|
| `parseCarries1` | Needed. The parser's only new fact. | §2.1 |
| `parseSettled1` | Needed, but subsumed: `parseCarries1` and `onceWordsSettled1` give it without a walk. | §2.2 |
| `fuelEnough1` | Not needed. Not stated. | §4 |

## 4. `fuelEnough1`, and "the parser is total on slice 1"

- **For the source, fuel can't make either top theorem false.** `parse1`
  is the meaning the theorems are about, so whatever tree the parser gives
  is the program, and both theorems start from "`formatWithin source = Ok
  output`", which already says the source parsed. The recursion's fuel
  running out is a failure (`Parse.recursiveWithFuel`'s `Zero` is
  `fatal`); a loop's is a quiet stop (`blockLines`, `suffixes` and the
  comma lists return what they have, `Parser.sw:737`, `:1497`, `:2134`)
  [source]. A quiet stop reads less, and `parseCarries1`'s spec is about
  what was read, so its walk needs no fuel fact either. That the loops'
  fuel is always enough is a fact about agreeing with the Rust parser,
  which the twin gate checks and no slice 1 theorem states.
- **For the output, read-back proves the parse succeeds**, fuel included:
  `runsTree` is `Parse.runsRecursiveWith` with each child shorter, and
  `ReadBackRuns` has the loops' fuel (`runsCommaListFrom`'s `enough`,
  `listFuelEnough`, `tupleFuel`) [source].
- **"Total on slice 1 inputs" would be false as a replacement**: a file in
  the alphabet can fail to parse (a closer at its item's column). The true
  form of it is `readsBack1`, which is being assembled (SW-4013).

## 5. Conditions no lane discharges

From SW-4003's list and from §1. Each is a hypothesis of a merged theorem
that glue will meet.

1. **`good` (`GoodItem`) for the source's items: no lane, and false of
   two tokens in the slice.** `parseShaped1` and `parseLexical1` (and
   `parseCarries1`) assume every item's text is one its kind `Spells`.
   - `Syntax.Proofs` proves the lexer complete for printed pieces
     (`lexPrinted`), and nothing about what a successful `lex` of an
     arbitrary source gave (NOTES.md says so: "`lexCovers` for every
     source" is not proved).
   - `List.map` lexes as one `Lower` token and `1e3` as a `Float`
     [computed: `qualifiedIsLower`, `exponentIsFloat`]. Both pass the
     alphabet, `within1` and `lexical1`, and `holdsOn` is true of a file
     using them. `Spells Lower` allows no `.` and `Spells Float` no
     exponent, so `good` is false of that file and no top theorem covers
     it.
   - SW-4010 (in progress) plans the inversion "`textLexesAs text kind`
     gives `Spells kind text`", which is false of the same two; it will
     meet this.
   - Decision D-A below.
2. **`laidOut` and the comments' shape for the source**: `lexLaid1`
   (§2.3). New ticket.
3. **`plain1` of the source can't be discharged**: K1's file (a comma
   starting its line before a closer) parses and isn't `plain`.
   `settledHomed`, `bareSettles` and so `settled1` of the tree are proved
   only under it. Either both top theorems carry it, or slice 1's driver
   refuses a source that isn't `plain`, as it refuses a token outside the
   alphabet. Decision D-B below. SW-3998 (`settledAnyLayout`) is the
   ticket that would remove it.
4. **Rule N does nothing to the output** (the sketch's `printedKeeping`
   and `printedSettle1`, in SW-4011's title, not done; SW-4016's scope
   ends at `printedHangs`). Read-back reads the output's leaves; the
   driver settles them first. Needed:
   - a general "settled leaves stay as they are": `homeIdle`, `commasIdle`
     and `arrowsIdle` exist but are joined only for `lexed.settled`
     (`settledIdempotent`);
   - that the printed leaves are homed, bare and trimmed, from `T.settled1`
     and where the rules put a closer that holds a comment (it starts its
     line);
   - `plain1` of the output: no comma starts a line (`hangs` has it), no
     `->` comes before a comma, closer or `->`, and the first token is
     `def`.
   This is `onceWordsSettled1` run backwards, and its statement should be
   settled the same way before a lane starts. No ticket yet.
5. **The file level of the output.** `printLexes1` is one declaration's
   text at column 0. The driver prints a file: declarations and their
   own-line comments joined by the file loop (`printedBy`). That the
   file's text lexes to the declarations' leaves in order, that it passes
   the alphabet, and that it has no last comma (`noLast`, for
   `settledOnceNone`) are glue's by the sketch (`printedAlphabet`), with
   no statement yet.

Smaller, for glue's brief:

- **There is no slice 1 driver.** `formatWithin` is slice 6a's
  (`Slice6a.sw:291`). Glue defines `formatWithin1`.
- **The passes' theorems take `within1` of the parse; the driver tests
  the tidied tree.** `formatWithin1` should test the parse (then
  `commaKeepsWithin` carries it), or glue proves that tidying can't bring
  a tree into the slice.
- **`calm` across read-back**: `commaFree` and `lexical1` of `read` from
  `read.calm = T.calm`: two small lemmas, not stated anywhere.
- **`Decl.real`** (no word's text is layout), which `printedSpellsSettled`
  takes: check that SW-4010 derives it from `lexical1`.
- `FrameRest.others` has SW-4017.

## 6. Proof tickets

Estimates are agent time, from today's actuals: SW-3967 (48 parser
theorems, Sonnet) 45 min; SW-4006 (`bareSettles`, 78 theorems, Sonnet) 35
min; SW-4000 33 min.

| # | Ticket | Model | Est. | After |
|---|---|---|---|---|
| A | `parseCarries1`, first half: the spec (`Carried`), its `ReadsIn` combinators, the lift of every `Out` fact by `readsWeaken`, atoms, brackets and comma lists, arguments and applications, and the recursion's knot | Opus | 60 min | now |
| B | `parseCarries1`, second half: the operator ladder, `expr`, `block`, the `def` frame, groups and the file | Sonnet | 60 min | A |
| C | `parseSettled1` from `parseCarries1` (used as stated) and `settledIsWords`: `groupsOf` only splits; cut the words at each `def` | Sonnet | 25 min | now |
| D | `onceWordsSettled1`: `laidOut` and `plain1` kept by `withoutLastCommas`; `bareSettles`; `endsOn` to `trailsBack` across bare commas; trimming keeps `--` | Sonnet, Opus if the look-back invariant sticks | 45 min | now |
| E | `lexLaid1`: `laidOut` and the end from `assemble` alone; a comment's and a closer's or `->`'s text from `item`'s soundness | Opus | 60 min | now |
| F | `good` for the source (§5.1): lexer soundness per token, in the form D-A chooses | Opus | 60–90 min | D-A |
| G | Fable, paper: state §5.4 (rule N does nothing to the output) and §5.5 (the file level), as this note does for the parser | Fable | 30 min | SW-4016's `printedHangs` statement |

A is Opus because the spec and the knot are the design; once they exist
B is the routine walk `ParseWalk` already is. C, D and E touch no file
A and B touch.

## 7. Decisions

- **D-A (Matt, scope): are qualified names and numbers with an exponent
  in slice 1?** They are today, by the alphabet and `within1`, and the
  lexer's `Spells` leaves them out, so the top theorems can't cover a
  file that has one. Options: narrow `within1` (an atom's text has no `.`
  and no exponent; such files wait for a later slice), or widen `Spells`
  and the lexer's proofs to them. Recommendation: narrow now, as SW-4000
  narrowed to lower-case names; widen with the slice that brings `.`.
- **D-B (Matt, what the theorem promises): `plain1`.** Carry it as a
  hypothesis of both top theorems, or have slice 1's driver refuse a
  source that isn't `plain`. Recommendation: the driver refuses, so the
  theorems read "whatever `formatWithin1` formats"; SW-3998 widens it
  later.
