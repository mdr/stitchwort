# Slice 1 of the proved formatter: the sketch (SW-3955)

Fable, 18 November 2026. Paper and probes. Ticket 13 of
[the proof plan](self-hosted-fmt-proof-plan.md) §7: the plan for proving
slice 1's program (SW-3950) before the proof lanes (tickets 14 to 20)
start.

How claims are marked: **[checked]** `stitchwort check` accepted it in a
scratch copy of `tools/fmt`; **[run]** I ran the program on the inputs
named; **[source]** read in the code, place given; **[inferred]** my
reasoning; **[estimated]** my estimate.

## In plain words

**The problem.** Slice 1's program matches Rust on every sampled
declaration, but the samples are code people wrote. The proofs are about
every file in the slice, so anything false of an odd file would be found
in the middle of a proof lane.

**The change.** The predicates and top statements are written out and
checked; the program was run on 9,900 generated files with comments, blank
lines and line breaks in every gap; and each statement was tested on what
came back.

**What it should do.** The proof lanes start from statements that held on
5,611 formatted files, with the false ones already found:

- **Slice 1 is provable as planned, after two fixes to the rules.** Both
  bugs are in the Rust formatter too.
  - A bracket in a `def`'s type with a comment after its `(` prints a `)`
    that doesn't parse (9 files). Rust's own check catches it and leaves
    the file unchanged; the Stitchwort formatter has no such check.
  - A blank line before the first item of a list of plain values isn't
    printed but still breaks the lines around it, so formatting twice
    gives two answers (3 files).
- **The tree keeps more blank-line flags than the printer writes back.**
  Reading the output back gave a different tree for half the files
  (2,803 of 5,611), by those flags alone. The statement is restated with a
  small function that clears the flags the rules never read.
- **The continued-line rule (K3a) holds, with a predicate that needs
  columns.** It is 30 lines, it held on all 6,122 outputs but the 9 that
  don't parse, and `Std.Doc`'s theorems give the columns it needs.
- **The count is higher than the plan's:** 950 to 1,400 theorems against
  550 to 850, mostly the parser, which has about 58 functions on slice 1's
  path, not 25.

## 1. The predicates, written out

All of §1 is in one file that `stitchwort check` accepts with 7 goals
open (the theorems) and no error [checked], but for `printParses1`'s
`shaped` and `lexical` hypotheses, whose predicates are named here and
not written (§1.5). It isn't in the repo: a file of open goals in
`tools/fmt` would show in every project check. The first proof lane to
need a predicate copies it from here.

### 1.1 `within1`, and the two checks

`Expr.within1`, `Header.within1`, `Decl.within1`, `SourceFile.within1` and
the alphabet `Tok.within1` are in `tools/fmt/src/Fmt/Slice1.sw` as SW-3950
wrote them, and need no change for the statements. Every tree-side theorem
takes `file.within1 = True`; §5.2 says why the alphabet can't replace it.

### 1.2 `Settled` for closers, commas and `->` (K1)

Stated of the tree's tokens in order (`Decl.words`: the header's and the
value's `Expr.words`), with no layout:

```stitchwort
--| A declaration's tokens in order, commas left out (the tree has none).
def Decl.words: Decl → List Word
  | Definition _ header (Assigned colonEq value) =>
    [fixedWord "def" header.keyword, header.name, fixedWord ":" header.colon] ++ header.result.words
      ++ [fixedWord ":=" colonEq]
      ++ value.words
  | _ => []

--| Closers, newest word first: a closer holds a trailing comment only if
--| it has own-line comments or the code before it, closers aside, ends
--| with a comment (K1's `homed`; commas aren't in the list, which is
--| rule 1 walking past them).
def homedBack: List Word → Bool
  | [] => True
  | [word, ..earlier] =>
    (!(isCloserText word.text && word.trails) || earlier.isEmpty || word.noted || trailsBack earlier)
      && homedBack earlier

--| `->`: no trailing comment on it and no own-line comment after it
--| (rule 3).
def arrowsBare: List Word → Bool
  | [word, next, ..rest] =>
    (operatorTok word.text != Some Arrow || (!word.trails && !next.noted)) && arrowsBare [next, ..rest]
  | _ => True

--| A comment as rule N leaves it and the lexer reads it: `--`, no line
--| break, no space at its end (rule 5).
def commentText (text: Text): Bool := text.startsWith "--" && !text.contains "\n" && !text.endsWith " "

def Comments.texts (comments: Comments): List Text := comments.above.map (note => note.text) ++ comments.after.toList

def Decl.settled1 (decl: Decl): Bool :=
  homedBack decl.words.reverse
    && arrowsBare decl.words
    && decl.words.all (word => word.comments.texts.all commentText)

def SourceFile.settled1 (file: SourceFile): Bool :=
  file.decls.all Decl.settled1 && file.end.texts.all commentText && file.end.after.isNone
```

- **Closers** are K1's `homed` (`tools/fmt-sketch/src/Settled.sw`) moved
  from leaves to words. `trailsBack` is already in `Rules.sw`: the rules
  ask the same question to decide whether a closer needs a line of its
  own.
- **Commas** need no clause. The tree has none, so the comma clause
  (`settledCommasBare`) is the parser layer's reason that dropping them
  loses no comment.
- **Held on every tree tried** [run]: `settled1` was true of the tidied
  tree of all 5,611 formatted sources and of every output that parses.

### 1.3 Blank lines: `calm`

The tree's `blankBefore` is set on every token and every own-line comment
(`Leaf.word`, `Syntax/Expr.sw:36`), and the rules read only some of them
(`Word.leading`, `notesAbove`, `closerNotes`, the file loop). `calm`
clears the rest:

```stitchwort
--| A token's comments with the blank-line flags the rules never read
--| cleared: the flag below the comments is read above an item with no
--| comments and below any comments that aren't a closer's; the first
--| comment's flag only above an item.
def Comments.kept (comments: Comments) (item closer: Bool): Comments :=
  let above := match comments.above with
    | [] => []
    | [first, ..rest] => [{ first | blankBefore = first.blankBefore && item && !closer }, ..rest]
  let below := if comments.above.isEmpty then item else !closer
  { comments | above, blankBefore = comments.blankBefore && below }

def Word.kept (word: Word) (item closer: Bool): Word := { word | comments = word.comments.kept item closer }

--| The expression with only the blank-line flags the rules read. `item`:
--| it is an item of a tuple or list.
def Expr.calm (expr: Expr) (item: Bool): Expr := match expr with
  | Atom kind word => Atom kind (word.kept item False)
  | Paren open inner close => Paren (open.kept item False) (inner.calm False) (close.kept False True)
  | Tuple open items comma close => Tuple (open.kept item False) (calmAll True items) comma (close.kept False True)
  | ListOf open items comma close => ListOf (open.kept item False) (calmAll True items) comma (close.kept False True)
  | App head arguments => App (head.calm item) (calmAll False arguments)
  | Infix kind left operator right => Infix kind (left.calm item) (operator.kept False False) (right.calm False)
  | Prefix operator operand => Prefix (operator.kept item False) (operand.calm False)
  | other => other

def calmAll (item: Bool): List Expr → List Expr
  | [] => []
  | [expr, ..rest] => [expr.calm item, ..calmAll item rest]
```

`Decl.calm` keeps the first token's flags (the file loop reads them all)
and calms the rest; `SourceFile.calm` maps it over the declarations and
clears the end's own flag. §3.3 has the evidence and §5.1 the decision.

### 1.4 The continued-line predicate (K3a)

Stated of one declaration's printed leaves, with their columns:

```stitchwort
--| The block column in force: the innermost open bracket whose current
--| item started a line, else the type's or body's, else the `def`'s 0.
def inForce (blocks: List (Option Nat)) (top: Option Nat): Nat := match blocks with
  | [Some column, .._] => column
  | [None, ..rest] => inForce rest top
  | [] => top.getOrElse 0

def leftOf (column: Nat): Option Nat → Bool
  | Some block => column < block
  | None => True

--| The leaves after a declaration's `def`, as the parser's line rule
--| needs them: a leaf that starts a line is right of the block column in
--| force; a closer that starts a line is left of the column its
--| bracket's current item started a line at; no comma starts a line.
--| `blocks` has, for each open bracket, that column for its current
--| item; `top` the same for the type or the body; `start`: the next leaf
--| starts an item, the type or the body.
def hangsFrom (blocks: List (Option Nat)) (top: Option Nat) (start: Bool): List Leaf → Bool
  | [] => True
  | [leaf, ..rest] =>
    let column := leaf.token.column
    let starts := leaf.token.lineStart
    let kind := leaf.token.kind
    if kind.isCloser then
      match blocks with
        | [block, ..outer] => (!starts || leftOf column block) && hangsFrom outer top False rest
        | [] => False
    else if kind == Comma then
      match blocks with
        | [_, ..outer] => !starts && hangsFrom [None, ..outer] top True rest
        | [] => False
    else if (kind == Colon || kind == ColonEq) && blocks.isEmpty then hangsFrom [] None True rest
    else
      let right := !starts || column > inForce blocks top
      let (opened, above) :=
        if start && starts then
          match blocks with
            | [_, ..outer] => ([Some column, ..outer], top)
            | [] => ([], Some column)
        else (blocks, top)
      if kind.isOpener then right && hangsFrom [None, ..opened] above True rest
      else right && hangsFrom opened above False rest

--| One declaration's leaves, from its `def`.
def hangs: List Leaf → Bool
  | [first, ..rest] => first.token.kind == KwDef && first.token.column == 0 && hangsFrom [] None False rest
  | [] => True
```

**Why it isn't "right of the limit".** The plan's wording has one limit.
The parser has one per expression that starts a line: `expr`
(`Parser.sw:621`) sends such an expression to `block`, which reads it with
the limit set to that first token's column, and `blockLines`
(`Parser.sw:709`) then treats the next line-start token at that column as
a new statement [source]. Two things follow:

- The limit is the column of the innermost enclosing item that started a
  line, so the predicate carries a stack of them.
- `stopsByLine` lets a closer or comma inside brackets start a line
  anywhere, but `blockLines`' test has no such exception. A closer at its
  own item's column is refused: `def d: A := [⏎  a,⏎  b⏎  ]` gives
  "expected an expression, but found `]`" from the compiler's parser
  [run]. That is the second clause, and it is exactly what the type-bracket
  bug breaks (§3.1).

The plan's third disjunct, an infix-only operator at the limit, isn't in
the predicate: the printer never uses it (a chain's operators are nested
2), so the read-back needs the parser to accept it only for sources.

**Is this the blind-alley signal?** The plan's signal was "the predicate
needs the engine's actual columns". It does need columns, and they are
there: `Doc.Proofs.Event` is `{ word, start: Option Nat }`, the column a
word starts its line at, and `printPuts` and `printLays` state their
`spec` over those events (`Places.sw:35`, `:2186`; `Lays.sw:1093`
[source]). So the rules layer proves `hangs` of the events and the
read-back consumes it. I read that as settled, not as a blind alley; the
open part is the size of the rules' `Lays` lemmas with columns in the
spec (§6).

**Held on every output but the nine that don't parse** [run]: `hangs`,
evaluated by the program on each output's leaves, was true of 5,602 of
5,611, and false of exactly the 9 files of §3.1. A Python copy of the
predicate gave the same on 6,122 outputs.

### 1.5 What each layer must establish

| Predicate | Says | Established by | Used by |
|---|---|---|---|
| `within1` | the tree is in the slice | `formatWithin`'s check; kept by P2 and `calm` | every tree-side statement |
| `Shaped1` | the tree is one the parser can give: an application's head isn't an application; an argument is an atom, a bracket or a prefix on one; `Infix` operands sit at their ladder levels; a tuple has two items or more; each `Atom`'s kind is a name or numeral | parser (walk) | read-back, as its induction's hypothesis |
| `settled1` | §1.2 | rule N, then the parser carrying it to the tree | rules (`printedSettle1`) |
| `Lexical1` | each `Word`'s text lexes as one token of its kind; a bracket's `Word` has its bracket's text; an operator's text is in `operatorTok`'s table | parser (walk), from the lexer's theorem per token | lexer read-back |
| `Spells` | the printed leaves, layout and commas aside, are the tree's words in order with their comments; a comma between each two items | rules and spelling | read-back |
| `hangs` | §1.4 | rules, through `printLays`' events | read-back |
| glue facts | a `Prefix` operator is glued to its operand unless `prefixGap` writes a space; call elements have a space between; a `-` argument is glued to what follows and not to what precedes | rules (joins) | read-back, at `argumentPrefix` and `negativeNumeral` |
| `calm` | §1.3 | passes (`calmTwice`), rules (`calmPrints`) | glue |

`Shaped1` and `Lexical1` are named, not written out: they follow the
parser function by function and the parser lane writes them first, as the
stage 3 sketch asked.

### 1.6 The top statements

```stitchwort
--| A source as slice 1 reads it: lexed, settled, parsed.
def parse1 (source: Text): Result SourceFile Text := match lex source with
  | Ok lexed => parseFile lexed.settled
  | Err message => Err message

--| The same program.
theorem formatWithinKeepsMeaning ∀ (source output: Text) (lexed: Lexed)
    (lexes: lex source = Ok lexed)
    (quiet: parksComment lexed.leaves = False)
    (formats: formatWithin source = Ok output):
    ∃ (before after: SourceFile) => parse1 source = Ok before ∧ parse1 output = Ok after
      ∧ after.meaning = before.meaning

theorem formatWithinIdempotent ∀ (source output: Text)
    (formats: formatWithin source = Ok output):
    formatWithin output = Ok output

theorem formatWithinKeepsComments ∀ (source output: Text) (before after: Lexed)
    (formats: formatWithin source = Ok output)
    (lexedBefore: lex source = Ok before)
    (lexedAfter: lex output = Ok after):
    CommentsKept before after

--| Where the layers meet: printing a tree the parser could have given,
--| tidied, and reading it back gives the tree, up to the blank lines the
--| rules don't keep.
theorem printParses1 ∀ (file: SourceFile)
    (within: file.within1 = True)
    (shaped: Shaped1 file) (lexical: Lexical1 file)
    (settled: file.settled1 = True)
    (bare: file.withoutTrailingCommas = file):
    ∃ (read: SourceFile) => parse1 file.printed1 = Ok read ∧ read.calm = file.calm
```

with `calmTwice`, `calmPrints` (`file.calm.printed1 = file.printed1`) and
`calmMeans` (`file.calm.meaning = file.meaning`) beside them, and the
refusals as the stage 3 sketch has them (`formatWithin` answers exactly
when the source lexes, passes the alphabet, parses and is within the
slice).

Three things differ from the stage 3 sketch's top statements:

1. **`printParses1` is up to `calm`** (§3.3, §5.1).
2. **`formatWithinKeepsMeaning` carries `quiet`** (§3.4): the driver
   parses twice when a comma before a closer holds a comment, and the
   theorem that the two parses agree isn't in any layer yet.
   `formatWithinIdempotent` needs no `quiet`: the output has no comma
   before a closer.
3. **There is no `format = print ∘ tidy ∘ parse`** to copy the toy's
   glue from: `Lexed.tidied` (`Passes.sw:431`) is the driver, and
   `tidiedIsTidy` (it is `tidy` of the parse when `quiet`) is a glue
   lemma.

## 2. Statements per layer

Counts are theorems [estimated], from the functions on slice 1's path
[source: counted in the files named] and the toy's measured rates
(SKETCH.md §5).

| Layer (ticket) | Interface statements | Behind them | Count | `Std.Doc` and std theorems used |
|---|---|---|---|---|
| Lexer (14) | `lexCovers`; `lexWord1` (a text that `lexesAs` a kind, then a piece it may be followed by, lexes to that token); `lexPrinted` (pieces with `Pairs follows` lex to their leaves, with columns, line starts and blank lines); `operatorTokLexes` | one read-back per token kind of the alphabet (29 kinds, 7 with a Unicode spelling), comments, line breaks and indentation | 90–130 | consumes `printedJoins`' `Pairs follows` |
| Rule N (15) | the six `settled…`; K1's `settledHomed` and `settledAnyLayout`; `barsQuiet1` and `letsQuiet1` (under the alphabet the bar and `let` clauses do nothing); `bareSettles` (§3.4) | three live passes over the leaves (rule 1, commas, `->`) and the trim | 150–230 | none; its partner `printedKeeping` is in the rules layer |
| Parser (16) | `parseShaped1`, `parseSettled1`, `parseLexical1`, `parseCarries1`, `fuelEnough1` | about 58 functions that perform `Parse` on slice 1's path and about 30 pure look-aheads (below) | 230–320 | `Parse.Gives`, `givesThen`, `givesLoop`, `readsInPeek`, `runsRecursiveWith` |
| Read-back (17) | `readsBack1`: leaves that `Spells` a tree, `hangs`, with the glue facts, parse to a tree with the same `calm`; first `blockOneLine` (under `hangs`, `block` reads one line and `blockLines` doesn't go round) | about 35 functions that build slice 1's nodes; the `Item` facts (`glued`, `afterOperand`, `depth`) recomputed from printed leaves | 110–160 | none directly |
| Rules and spelling (18) | `printLexes1`, `printedSpells`, `printedHangs`, `printedKeeping`, `printedSettle1`, `calmPrints` | about 25 functions that build a `Doc`, each with words, `Uniform` and `Marked`, joins, and `Lays`; about 20 predicates on words (`trails`, `holdsTrailingComment`, `keptFront`) | 300–450 | `printedWords` (from `readingWords`), `printedJoins`, `printLays`, `printPuts`, `printIsPieces` |
| Passes (19) | P2: `commaKeepsWithin`, `commaBare`, `commaTwice`, and `settled1`, `Shaped1`, `Lexical1`, comments kept; `forallSame1`, `bracketsSame1`, `mergeSame1` (P1, P3, P4 change nothing in the slice) from one `walkSame1`; `calmTwice`, `calmWithin`, `calmMeans` | `Walk.sw`'s lemmas are proved; `commaKeepsFile` and `tidyKeepsMeaning` exist | 40–60 | none |
| Glue (20) | the three top theorems, the refusals, `tidiedIsTidy`, `printedAlphabet` (the output passes `formatWithin`'s first check), `printedQuiet` | | 25–40 | none |
| **All** | | | **945–1,390** | |

The plan said 550–850. Where the difference is:

- **The parser has about 58 functions on the path, not 25** [source:
  counted by reading the function lists of `Parser.sw` and
  `DeclParser.sw` against the calls from `exprInline` down; not traced
  by a tool, so within a few either way]. The plan counted the
  ladder. On the path as well: ten shared readers (`peek`, `at`, `bump`,
  `expect`), `expr`, `block`, `blockLines` and `statement` (every body
  below its `:=` and every item on its own line goes through `block`),
  the logic chain, the `def` frame, and the look-aheads `exprInline`
  tries before it reaches an operator (`lambdaAhead`,
  `lambdaResultType`, `implicitBinderAhead`, `piBinderAhead`). Most are
  permanent: later slices use them unchanged.
- **Rules and spelling are the toy's rate on more complex rules**: the
  toy's 460 theorems for 36 rule functions is 12.8 a function; 25
  functions at that rate is 320, and these use `Choice`, `IdGroup`,
  `IfBroken`, `Fill`, `Displaced` and `CloserLine`, which the toy's didn't.

## 3. The counterexample search

**How.** A generator (Python, in the lane's scratch folder) makes files of
one to three `def`s from random slice 1 trees, six mixes of: comments
after any token and on lines of their own, blank lines, line breaks at
legal columns, closers and commas at odd columns, glued and spaced `-`
and `!`, glued call elements (`f(x)`, `g[x]`, `2a`), trailing commas, and
lists of 40 plain values. Each file went through the interpreted
`Fmt.Twin` (the main checkout's `stitchwort run`; 850 MB to 1.5 GB), with
two stages added in the scratch copy: the tree's words with their comments
and flags, and the predicates of §1.

| Check, on each formatted file | Files | Failed |
|---|---|---|
| The output formats to itself | 5,611 | 12: families A (9) and B (3) |
| The output's tree is the source's tidied tree (the dump, no comments) | 5,611 | 9: family A, which doesn't parse |
| Comments in order, by text | 5,611 | 0 |
| Words, comments and holders the same, flags aside | 5,611 | 9: family A |
| The same with every blank-line flag | 5,611 | 2,803 |
| The same after `calm` on both sides | 5,611 | 24: family A (9) and family B (15) |
| `hangs` of the output's leaves (§1.4) | 5,611 | 9: family A |
| `settled1` of the source's tidied tree | 5,611 | 0 |
| Byte for byte Rust's `fmt -` (first 511 files only) | 511 | 57: 53 glued pairs (§3.5), 4 family D |
| No code line over 120 columns that could break | 5,611 | 0 |

9,900 files were generated; 5,611 were within slice 1 and parsed. The
rest were refused: a comma or closer at its item's column (§1.4, which
Rust refuses too), comparison chains, a token outside the alphabet.

Deep and long inputs, one each [run]: 300-deep `(`, `[`, tuples, `-` and
`!`; 300-deep `a ++ (…)` and `(… a)`; 400 arguments; 400 `->`; 300
operands of `f (a * -b) [c, d]`. All formatted to themselves and
identical to Rust. A chain of 1,500 `+` didn't finish in 120 s
interpreted (§7).

### 3.1 Family A: a bracket in the type prints a `)` that doesn't parse

```stitchwort
def d: ( -- t7
    a -- t9
  ) -- t10
  := b
```

Both formatters print [run]:

```
def d: ( -- t7
    a -- t9
    ) -- t10
      :=
  b
```

`a` starts a line at column 4, so it is read as a block at 4, and the `)`
at 4 is taken for the block's next line: "expected an expression, but
found `)`". Rust reports "formatter bug … the output doesn't parse (file
left unchanged)"; the Stitchwort formatter has no check and writes it.
The same bracket in the body prints its `)` at 2 and is fine.

- **Which statement it falsifies:** `printParses1`, at `hangs`' closer
  clause. `formatWithinIdempotent` is false of it as stated.
- **Fix (recommended):** in the rules, both formatters (D3677: a bug in
  both is fixed in both). A closer that takes a line of its own after a
  comment (`Word.leaf`'s `ownLine`, S39) goes at the bracket's
  indentation, as the comma brackets' closers do, not at the
  continuation indent its contents were pushed to. The test is the file
  above, on both sides.
- **The other fix** is in the language: let a closer or comma inside
  brackets start a line at any column, as `stopsByLine` already does.
  §7 has it as a question; slice 1 doesn't need it.
- **Fixed (SW-3962):** both formatters put such a closer on a
  `CloserLine` keyed by its opener, as after own-line comments, so the
  file above prints `)` at 0. `tools/fmt/NOTES.md` has the details.
- **If neither lands before ticket 17:** the read-back lane proves
  `hangs → reads back`, which is true, and ticket 18 can't prove
  `printedHangs` for `parenDoc` in a type. So the fix goes first.

### 3.2 Family B: a blank line before a filled list's first item

```stitchwort
def d: A := g [

  f, a]
```

Both formatters print `def d: A :=⏎  g⏎    [f, a]`, and from that
`def d: A := g [f, a]` [run]. The first item of a list that fills its
lines (`cells`, D3572) gets `[BreakParent, Blank]` from `Word.leading`
for its blank line; in mid-line the `Blank` writes nothing, but the
`BreakParent` still breaks every group around it.

- **Which statement it falsifies:** `formatWithinIdempotent` (3 files),
  and `calmPrints` as §1.3 has `calm`, which keeps that flag (those 3
  and 12 more, where the list was the first thing after `[` each time).
- **Fix (recommended):** the first cell of a filled list isn't an item
  for blank lines (`itemAround`'s `item` false for it, `keep_blank` in
  Rust), and `calm` clears the flag there too. The test is the file
  above: formatted twice, one answer.

### 3.3 Blank-line flags: reading back gives another tree

Of 5,611 files, 2,803 read back as a tree that differs from the one
printed in some `blankBefore` [run]. Three sources:

- **Flags the rules never read** (most of them): a blank line before an
  operator, a closer, a later argument, or a first own-line comment that
  isn't above an item. The parser sets the flag, the printer drops the
  line, the read-back has no flag.
- **Family C, a blank line the printer adds:** `[⏎  2,⏎  Foo -- t7⏎] --
  t8` prints with an empty line before `]` in both formatters [run]: the
  bracket's `SoftLine` breaks, then the closer's own-line `HardLine`
  (S39) breaks again. The read-back has a flag the tree didn't. It is
  stable, so no statement is false of it once flags on closers are
  cleared, but it looks unintended.
- **Family B**, above.

So `parse (print t) = Ok t` is false of half the trees, and
`printParses1` is stated up to `calm`. After `calm` on both sides
24 files differ: the 9 of family A, and 15 of family B (its 3, and 12
more where the dropped line moves nothing else, so they still format to
themselves).

### 3.4 The driver parses twice

`Lexed.tidied` (`Passes.sw:431`) parses the settled leaves, and when a
comma before a closer holds a comment (`parksComment`) parses again from
the leaves with those commas taken out first (`settledBare`), which is
K1's option 1. So the tree that is printed is not `tidy` of the tree
`parse1` gives, and "the same program" needs a theorem no layer has:

```stitchwort
theorem bareKeepsMeaning ∀ (lexed: Lexed) (plain bare: SourceFile)
    (parses: parseFile lexed.settled = Ok plain)
    (parsesBare: parseFile lexed.settledBare = Ok bare):
    bare.meaning = plain.meaning
```

It relates two runs of the parser on different leaves, which is a second
walk over every parser function. Three ways on:

1. **Narrow slice 1's theorem** with `quiet` (§1.6). Idempotence is
   untouched, since no output has such a comma. Costs nothing; leaves
   "the same program" unproved for files with a comment on a last
   comma.
2. **One parse** [inferred, not run]: move the last commas' comments as
   `withoutLastCommas` does but leave the commas in, bare and not
   starting their lines; settle; parse once; P2 drops the commas on the
   tree. Then `format` is print, tidy, parse and the toy's glue carries.
   It needs rule N to treat a bare comma that doesn't start its line as
   if it weren't there, which K1's search program can test in a few
   minutes before anyone builds it.
3. **Prove `bareKeepsMeaning`**: about 60–100 theorems [estimated].

Recommended: 1 for the proof lanes now, 2 as a ticket with its search
first, decided at slice 1's checkpoint.

**Outcome (SW-3964): way 2, with the comma keeping its line start.**
`Lexed.tidied` now parses once, from `Lexed.settledOnce`: each comma
before a closer has its comments moved as `withoutLastCommas` moves them
and stays in bare, then rule N runs; P2 drops the commas on the tree. So
`tidiedIsTidy` is by computing, and `parse1` should read
`parseFile lexed.settledOnce` (on the output, which has no such comma,
that is `parseFile lexed.settled`). The search [run: generated slice 1
files, `tools/fmt/dev/probe.py`'s generator, three seeds]:

| Check | Files | Result |
|---|---|---|
| Rule N on the bare-comma leaves, commas then dropped, against `settledBare` (`bareSettles`) | 5,400 (2,679 that parse) | 0 differ |
| The comma not starting its line (the sketch's way 2): files the old driver refuses that it parses | 3,000 | 54, all refused by Rust: rule N is the same, the parser isn't |
| The comma keeping its line start: refusals as the old driver | 3,000 | the same |
| Its four trees against the old driver's (dumps, no comments) | 1,458 that parse | the same |
| Its formatted text against the old driver's | 1,458 | 24 differ; Rust's on 22, the other 2 only §3.5's glued pairs; the old driver matched Rust on none |

The 24 are a family the old driver missed: a comma that starts the
closer's line with no comment of its own, after a line ending in a
comment, gets the closer's trailing comment from rule 1 and rule 2 puts it
above the closer, where Rust, deleting the comma, leaves it on the closer
(`parksComment` looked only at the comma's own comments). A second: on
K1's own case the old driver's bare parse failed (the closer, now first on
its line, sits at the item's column) and it fell back to the plain parse
silently. Both are tests in `Tests/Slice1.sw`. `bareSettles` is searched,
not proved: under `plain1` no comma before a closer starts its line, so
its proof is rule 1, 2 and 3 run with a skipped leaf more.

**Family D, found here:** `withoutLastCommas` gives a line-starting
comma's trailing comment no blank line above it (`comment.unspaced`,
`Settle.sw:292`), where Rust, deleting the comma from the text, sees the
comma's own blank line: `g -- t12⏎  -- o13⏎⏎ , -- t14⏎)` prints an
empty line before `-- t14` in Rust and none in the Stitchwort formatter
[run; 4 of 511 files]. Fix: the moved comment takes the comma's
`blankLines`. No statement is false of it; the harness would report it.

### 3.5 Glued call elements: the tree can't tell, and only `)(` still differs

SW-3950 named two pairs where Rust copied the source's gap and the rules
write a space: `)(` and `f[x]`. SW-4459 made Rust space the second, as the
rules already did, so `)(` is the one remaining difference: `spacing.rs`
keeps it. The search found the class is every pair of adjacent call
elements the lexer splits without a space [run, 53 of 511 files]: `2a`,
`3.5xs`, `)a`, `2(`, `](`, `)[`, `]a`, `)2`, `a[`. Rust kept them glued
then; both formatters now write `2 a`. Nothing is false: the tree is the
same either way and each formatter is stable. Only a `)(` file can drift
now; none is in the repo sample.

### 3.6 Prefix `-` and `!`

No failure in 5,611 files, with `-` and `!` glued or spaced at random
before atoms, brackets, numerals and each other, at line starts and after
operands. The cases traced by hand against `unary`, `negativeAtom`,
`argumentPrefix` and `negativeNumeral` [source]: `-1 n` and `- 1 n`,
`a -1` and `a - 1`, `a - -1 n`, `- -x`, `!-x`, `-(a) b`, an argument
`-x` starting a line. Each prints so that it reads back as itself. `f
!!b` is still refused where Rust reads it (K4's finding, unchanged).

## 4. Probes for F9 and F10

### 4.1 F9: induction over the real tree [checked]

- **`Expr.size`, `Expr.induct` and `Expr.inductMem` are not generated**
  for the real tree: "`Syntax.Expr` has no `size`", and the same for the
  other two. The tree's types are defined together, and nothing is
  generated for those (`docs/syntax.md`, "Generated size and
  induction").
- **Structural recursion in a theorem works, with only the slice's
  arms.** A probe (`Expr.id1`, a rebuild of slice 1's nodes; `id1Same:
  e.within1 = True → e.id1 = e`, with `ids1Same` for the lists) was
  accepted first time: 8 arms of 37 constructors, two of `Infix`'s seven
  kinds as separate arms, the rest absent. Taking the `App` arm out gives
  `E-NONEXHAUSTIVE` naming `App _ _, _`; no arm outside the slice is
  asked for.
- **Time:** the probe's namespace rechecks in 1.2 s; a first check of the
  scratch project (the parser, the rules, the probe) takes 15–20 s.
- **List helpers:** slice 1's tree has one container, `List Expr`, so an
  induction is two theorems and its arm lemmas. That is under the fifth
  the plan set as the mark for reopening D3611, so no question to Matt
  from slice 1. `Walk.sw`'s 78 family proofs were written the same way,
  from a table.

### 4.2 F10: three parser functions with abilities [checked]

| Function | Equations | Unfolds under std's lemmas? |
|---|---|---|
| `addExpr` | none: it has no arms | yes. `Parse.givesThen mul (first held => ?)` is accepted, and the goal left is the bind of `operatorLinks …` and `Done (leftNested first x)`, which is `givesThen (givesLoop …)` and `givesDone` |
| `commaListFrom` | none | yes, after `match fuel` and one `givesThen` for `modes.peek`: the `Zero` arm computes to `Done ([current, ..found].reverse, False)` and the `Succ` arm to the match on the token |
| `suffixes` | `E-NO-EQUATION`: "it performs abilities … its arms are computations" | the `Zero` arm closes with `givesDone`. The `Succ` arm computes to four binds nested to the left (`bind (bind (bind (bind (left ()) …`), because its `if` tests `unitCall left() && …` in place. `givesThen` peels them from the outside, one stated predicate a level |

So none has equations and all three are usable as written. **SW-3443
isn't needed for slice 1.** The one reshaping worth doing is small and
keeps the Rust shape: bind `left()` once at the top of `suffixes`' `Succ`
arm and test the pure functions on it. In slice 1 `suffixes` only ever
returns its target (no `()` call and no `.` in the alphabet), so even
that can wait for slice 4.

## 5. The two decisions

### 5.1 `Comments.blankBefore`: keep the `Bool`, state the theorems up to `calm`

- **A `Bool` is the right shape, not a count.** The rules test only
  "more than none" and print at most one empty line.
- **The statements are not fine with it as the parser sets it**: on
  every token, where the stage 3 sketch (§1, item 2) asked for it only
  where the rules keep a blank line. §3.3 is the measurement.
- **Recommended: `calm` in the statements, the parser unchanged.**
  Where a flag is read depends on what the token is in the tree (the
  first token of a bracket's item, a closer, a declaration's first), so
  the parser can't decide it as it reads a leaf; it would be a pass over
  the finished tree, which is `calm`. Using `calm` only in statements
  changes no program and no hash. The other way round (the driver applies
  `calm` before P1, and `Parsed` says `file.calm = file`) gives the same
  theorems with plain equality, and is worth doing if the read-back lane
  finds the `∃ read` form awkward.
- **Cost:** about 20 theorems (`calmTwice`, `calmWithin`, `calmMeans`,
  `calmPrints` by arm), in tickets 18 and 19.
- **It must follow the rules.** `calm` is the rules' `keep` as a
  function, so a rule that starts or stops reading a flag changes it, and
  family B's fix does.

### 5.2 The two checks stay two

A lemma "the parser stays in the slice, given the alphabet" is false, and
no alphabet makes it true. These use only slice 1's tokens and parse to a
tree outside it [run, each answered "a construct slice 1 doesn't have"]:
`(+ 1)`, `(a +)`, `(+)`, `a < b < c`, `(a: T)`, `()`, `f()`, `(x := 1)`,
`f [x := 1]`, `(x: A) -> B`, `[x: A] -> B`, `def d (x: A): B := x`, and
two lines at one column (a block).

- **The tree check is the one the theorems use.** Every tree-side
  statement takes `within1`, and `formatWithin`'s second check supplies
  it.
- **The alphabet is for the parser lane, not for the theorems.** With
  "every token left is in the alphabet" as the walk's invariant, a branch
  that starts with `match`, `if`, `{`, `.` or `=>` is dead at its peek.
  Without it each such branch needs its own walk to show it gives a tree
  outside the slice.
- **The branches the alphabet leaves** (sections, a comparison chain, an
  annotation, `()`, a named argument, a Π type) each need a lemma that
  their result is outside the slice, and the Π type's drags in the
  parameter-group parser. A stronger first check would kill most of them
  at the peek: no `:` or `:=` inside brackets, no `(` directly before
  `)`, no operator but `-` and `!` directly after `(`, none directly
  before `)`. `Parse.Invariant` is any property of the items left that
  holds of every tail (`Reads.sw:64` [source]), so these fit. That is
  optional: it saves about 30 theorems in ticket 16 and adds a
  30-minute program change. Comparison chains and blocks can't be
  screened from the leaves, so the tree check stays either way.

## 6. Revised estimates for tickets 14 to 20

Agent minutes at 90 theorems an hour, the toy's measured middle. Past
lanes finished in 0.33 to 0.45 of their estimates (CLAUDE.md); these are
set from counts, so read them the same way.

**Before the proof lanes** (new):

| # | Ticket | Model | Est. |
|---|---|---|---|
| 13a | Family A: a closer on its own line in a type's bracket, both formatters, with the test | Opus | 45 |
| 13b | Family B: no blank line kept before a filled list's first item, both formatters, with the test; family D with it (`withoutLastCommas`' blank line) | Sonnet | 40 |
| 13c | One parse: K1's search on "a bare comma that doesn't start its line changes nothing in rule N", then `Lexed.tidied` as parse, tidy (§3.4, way 2) | Opus | 60 |

**The lanes:**

| # | Ticket | Theorems | Model | Est. | Plan's |
|---|---|---|---|---|---|
| 14 | Lexer for the alphabet | 90–130 | Sonnet | 75 | 90 |
| 15 | Rule N: the six, K1's two, the quiet clauses | 150–230 | Opus | 130 | Fable, 120 |
| 16a | Parser: shared readers, look-aheads, the `def` frame, `Shaped1` and `Lexical1` written out | 100–140 | Sonnet | 80 | 90 for all of 16 |
| 16b | Parser: the ladder's walk and carry, `block`, `fuelEnough1` | 130–180 | Sonnet | 110 | |
| 17 | Read-back, `blockOneLine` first | 110–160 | Opus | 90 | 90 |
| 18a | Rules: words, `Uniform`, `Marked`, joins, `printLexes1` | 130–190 | Sonnet | 100 | 120 for all of 18 |
| 18b | Rules: `Lays` with columns, `printedHangs`, `printedSpells`, `printedKeeping`, `calmPrints` | 170–260 | Opus | 150 | |
| 19 | Passes: P2's facts, the three identities, `calm` | 40–60 | Sonnet | 35 | 60 |
| 20 | Glue, `axioms` clean, the checkpoint | 25–40 | Opus | 45 | 45 |
| | **All** | **945–1,390** | | **815** | **615** |

**Order.**

- 14, 15, 16a and 19 depend on nothing found here and can start now.
- 13a and 13b go before 18: they change the rules 18 proves.
- 17 starts with `blockOneLine` and fixes `hangs`' final form; 18b
  starts when it has, since `hangs` is the spec its `Lays` lemmas carry.
- 16b after 16a's predicates; 20 last.

**Models.** Ticket 15 was Fable's in the plan. It is a proof lane, and
Fable's lanes are paper (CLAUDE.md); K1 already wrote the predicates and
searched them, so what is left is Opus's kind of proof (rule N ran 2.4
times over in the toy). 16 and 18 are each split so that the routine half
goes to Sonnet.

**Against the stop rules.** The plan's check is "within 1.5 times the
sketch's count", and this sketch is that count: 945–1,390, middle about
1,150. The plan's own 550–850 is passed at the sketch, by the parser
and the rules; if slice 2's sketch does the same, the 3,450–5,650 total
is nearer 5,000–8,000, which is under the 9,000 at which the plan asks
Matt.

## 7. Found on the way

For the orchestrator to file. None blocks 14, 15, 16a or 19.

- **Families A, B and D** (§3.1, §3.2, §3.4): tickets 13a and 13b.
- **Family C** (§3.3): the formatter adds an empty line before a closer
  that takes its own line after a comment. Both formatters; stable;
  looks unintended.
- **The compiler's parser refuses a closer or comma at its item's
  column** (§1.4): `[⏎  a,⏎  b⏎  ]`, "expected an expression, but found
  `]`". Inside brackets a closer is exempt from the line rule everywhere
  but in `blockLines`' test for a next line. User-visible language, so
  Matt's if it is to change.
- **Glued call elements no longer drift from Rust** (§3.5): SW-4459
  spaces all nine kinds of pair, not just two; `)(` is still kept.
- **The rules are quadratic on long chains** [run]: `Expr.size`,
  `trails` and `firstWord` rebuild `Expr.words` at each node. 300
  operands of a mixed chain took 71 s interpreted, 1,500 `+` over 120 s.
  The proofs don't mind; stage 7's speed gate will.
- **`formatWithin` has no run-time check, and family A shows what that
  means** until `printParses1` is proved: on such a file Rust leaves the
  file alone and the Stitchwort formatter writes text that doesn't
  parse.
- **Not done:** `Shaped1` and `Lexical1` are not written out; the
  statements below the top ones are named, not checked; the search's
  scripts are in `tools/fmt/dev/` (SW-3962); `check
  --counterexamples` was not run (the search here ran the program
  itself, which K1 found the stronger test); the one-parse design (§3.4)
  was not run.

## Sources

`self-hosted-fmt-proof-plan.md` in full; `tools/fmt-sketch/SKETCH.md`
and `src/Settled.sw`, `src/SettledProofs.sw`; `tools/fmt/NOTES.md` from
SW-3877 on; `tools/fmt/src/Fmt/Rules.sw`, `Spacing.sw`, `Slice1.sw`,
`Passes.sw` (the driver), `Twin.sw`; `Syntax/Parser.sw` lines 1–270,
540–830, 960–1392; `Syntax/Settle.sw`; `Syntax/Expr.sw` lines 1–200;
`crates/elab/src/std/Doc/Places.sw`, `Lays.sw`, `Words.sw`, `Joins.sw`
(the top theorems' statements); `crates/elab/src/std/Parse/Reads.sw`,
`Gives.sw` (statements); `crates/fmt/src/printer/rules.rs` lines
255–312. Not read: the proving guide beyond its sections on equations
and nested types; `Walk.sw` and the proof files beyond one family proof;
`DeclParser.sw` beyond `definitionParts` and `resultType`; the lexer.
