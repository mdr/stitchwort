# The real formatter's proof, stated: the sketch (SW-3820, stage 3)

Fable, 17 November 2026. Stage 3 of
[self-hosted-fmt.md](../../docs/proposals/self-hosted-fmt.md) §8, done as
[the toy's SKETCH.md](../toyfmt/SKETCH.md) and
[SKETCH-PLUS.md](../toyfmt/plus/SKETCH-PLUS.md) did it: everything stated,
almost nothing proved, and the statements checked for fit.

How claims are marked: **[checked]** `stitchwort check` accepted it in
this project; **[computed]** a `byComputing` example in
`src/Examples.sw`; **[run]** I ran the named command; **[searched]**
`check --counterexamples` found none (evidence, not proof); **[source]**
read in the code; **[measured]** counted with a command; **[inferred]** my
reasoning; **[estimated]** my estimate.

## 1. For stage 2: what the tree should and should not hold

This section is for the stage 2 lane. Each item is something the top
theorem `parse (print t) = Ok t` needs of the tree type. Stage 1's
`Leaf` (`{ token: { kind, text, column, lineStart }, trivia: { leading,
blankLines, trailing } }`) is right for the lexer and rule N and wrong as
the tree's leaf.

**What `meaning`, and so the tree, should not include:**

1. **No layout in a leaf.** No `column`, no `lineStart`, no comment
   `column`, no span or offset. The printer chooses all of them, so a
   tree that held them would differ from the tree of its own printed
   text, and `printParses` would be false of every reformatted file. The
   parser reads columns from the leaves and keeps none. The tree's leaf
   is a token's text (where it varies) and its comments: `Word` and
   `Comments` in `src/Tree.sw`.
2. **No count of blank lines, and no blank-line flag on every token.** A
   `Bool`, and only where the Rust rules keep a blank line (`rules.rs`
   lines 278–302 and 1092–1098 test `blank_lines_before > 0`, some only
   under `keep`) [source]. The parser drops the rest. A flag the printer
   doesn't reproduce is the same problem as a column.
3. **No commas.** After rule N no comma holds a comment
   (`settledCommasBare`, [searched] on stage 1's code, 8,501 cases), so a
   comma carries nothing but its presence. The tree keeps one flag,
   `trailingComma`, on the ten kinds P2 reads (`List`, `Tuple`, `Record`,
   `Fields`, `PatternList`, `PatternTuple`, `PatternRecord`,
   `Attributes`, `Import`, `RewriteRules`; `passes.rs`) [source]. The
   dump writes the `,` lines from the item list.
4. **No source slice for a `"""` text.** Its lines by value, without the
   indentation the printer chooses (§3.4's last row). A slice of the
   source changes when the block is re-indented.
5. **No `Error` or `Gap` constructor**, and no root for a lone
   expression (`Expression`): the formatter's parser is strict (§3.3).
6. **Nothing derived**: no token roles (`spacing.rs`'s `roles`), no
   node ids, no kind name stored beside a constructor that already says
   it.
7. **`meaning` forgets less than §3.4's table says.** The table's first
   row forgets every comment-free bracket pair. The compiler reads one:
   the pair around an application's head (`same_program.rs`'s header;
   `(f) x` parses as `App` with a `Paren` head [run: `dev tree
   --print`]). So `meaning` here forgets a pair only in the two places P3
   drops one (the type after a row, a parameter's whole type), a group's
   split only for groups P4 could have made, and `∀` only where P1 writes
   it. The rule: **`meaning` forgets exactly what a pass changes, where
   the pass changes it.** It is the trusted definition, so the less it
   forgets the less there is to trust.

**What the tree should have, so the passes and `meaning` are cheap:**

8. **The traversal, from the start.** One function per family that
   rebuilds a node from its traversed children and then applies a step
   (`src/Traverse.sw`). `meaning` and all four passes are that traversal
   with different steps, and no statement here uses the tree any other
   way except through the constructors of items 9–12.
9. **`Paren` as its own constructor** (open comments, inner, close
   comments), and **the two slots reachable as fields**: an `Effect` node
   with its row and the type after it as separate fields; a parameter
   with its type as one field.
10. **One parameter-group constructor** for `Param`, `Binder` and
    `LambdaParam` (a kind tag, the bracket, `auto`, the names as a list,
    the colon, the type, the default), and a header's, lambda's and `∀`'s
    parameters as a `List` of them, adjacent, not interleaved with other
    parts.
11. **A theorem's `∀` as `Option Comments`** on the header.
12. **Fixed tokens as `Comments` only** where the token has one spelling
    (a keyword, a bracket, `:=`): the constructor says which token it is,
    and `Lexical` has nothing to say about it. A token with a text
    (names, numerals, text pieces, operators with an ASCII and a Unicode
    spelling, if the formatter keeps the spelling as written; not
    checked) is a `Word`.
13. **Constructors by shape, kinds as a tag where shapes coincide**
    (`Binary`, `Pipe`, `Arrow`, `Iff`, `Membership`, `Range`, `Seq`,
    `PatternOr`, `PatternAppend` are all "left, sign, right"). Every
    induction then has tens of cases, not 98. The sketch goes further
    than stage 2 should (`Form kind parts` for everything without a
    freedom); the point is that the dump needs the 98 names and the
    proofs don't need 98 constructors.
14. **The lowering's three errors as `SourceFile → Option Text`, called
    inside `parse`**, so `format` is "parse, tidy, print" and the toy's
    glue proofs carry over word for word [checked: they did].
15. **Fuel = leaves left + 1** at each recursion and loop, with an
    `extra` passed in, so `fuelEnough` can be stated (§6): every call of
    the parser's `self` follows a read (spike K4, SW-3826).

Checked while writing this: `(x,)` does not parse, as an expression, a
type or a pattern [run], so P2 never turns a tuple into a bracket pair.

## 2. What is here

`tools/fmt-sketch/` is a project of its own (`check: open-goals: warn`),
with `syntax` a symlink to `../fmt/src/Syntax`, so the lexer and rule N
statements are about stage 1's real code, imported, not copied. `tools/fmt`
never sees it. `stitchwort check` here says "57 goals open" and no errors,
in about 1.3 s [run].

| File | Holds | Written or open |
|---|---|---|
| `src/Tree.sw` | the tree: 7 expression constructors, parameters, declarations, and `Kind`, the 98 Rust node kinds by name | written |
| `src/Traverse.sw` | `Slot`, `Steps`, the shared traversal | written; the termination checker accepts it [checked] |
| `src/Meaning.sw` | `Meaning`, `plainSteps`, `SourceFile.meaning` | written, complete |
| `src/Passes.sw` | P1–P4 as traversals, `tidy`, `tidySteps` | P1, P2 and P3's frame written; `Expr.standsAt` and `mergeGroups` open |
| `src/Format.sw` | `parse`, `format` | written; the grammar, the refusal check and `print` open |
| `src/Proofs.sw` | 8 definitions, 66 theorems | 44 theorems and 8 definitions open; 22 proved |
| `src/Examples.sw` | 7 cases of `meaning` | proved by computing |

The 57 open goals are 44 theorems and 13 definitions (5 of the program:
the grammar, the refusal check, the printer, `standsAt`, `mergeGroups`;
8 of the proof: `Shaped`, `Settled`, `Lexical`, `Spells`, `Printed`,
`SourceFile.comments`, `SourceFile.spelling`, `renderWith`).

**The node kinds.** The Rust `NodeKind` has 98 variants [measured: `awk`
over `tree.rs`], not the paper's 94. `meaning` covers all but `Error`:

| Kinds | Count | In `meaning` |
|---|---|---|
| `Paren` | 1 | forgotten after a row and as a parameter's whole type, if it holds no comment [computed: `pairAfterRowForgotten`, `pairAtHeadKept`, `pairWithCommentKept`] |
| `Param`, `LambdaParam` (and `Binder`, which P4 doesn't merge but which splits the same way) | 3 | a comment-free group whose type names none of its names is split, one group a name [computed: `groupSplit`, `dependentGroupKept`] |
| `Theorem` | 1 | `∀` present where P1 writes it [computed: `forallForgotten`] |
| the ten comma brackets of item 3 | 10 | the flag is `False` [computed: `commaForgotten`] |
| `Effect` | 1 | kept; it is where the first slot is |
| every other kind but `Error` | 81 | kept: the traversal goes into its parts |
| `Error` | 1 | never in a tree |

## 3. The top theorems, as stated [checked]

All in `src/Proofs.sw`, all proved from the open statements below them.

```stitchwort
theorem printParses ∀ (file: SourceFile) (width: Nat)
    (parsed: Parsed file)
    (bare: file.withoutTrailingCommas = file):
    parse (file.print width) = Ok file

-- The same program.
theorem formatKeepsMeaning ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    ∃ (before after: SourceFile) => parse source = Ok before
      ∧ parse output = Ok after
      ∧ after.meaning = before.meaning

theorem formatIdempotent ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    format output width = Formatted output

-- Totality and the refusals.
theorem formatAnswers ∀ (source: Text) (width: Nat) (tree: SourceFile)
    (parsed: parse source = Ok tree):
    format source width = Formatted (tree.tidy.print width)

theorem formatRefuses ∀ (source: Text) (width: Nat) (message: Text)
    (refused: parse source = Err message):
    format source width = Refused message

theorem formatRefusesOnly ∀ (source: Text) (width: Nat) (message: Text)
    (refused: format source width = Refused message):
    parse source = Err message

-- The rest of the must set (D3663).
theorem formatRoundTrip ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    ∃ (tree: SourceFile) => parse source = Ok tree ∧ output = tree.tidy.print width ∧ parse output = Ok tree.tidy

theorem formatSameTree ∀ (first second: Text) (width: Nat) (tree: SourceFile)
    (parsesFirst: parse first = Ok tree)
    (parsesSecond: parse second = Ok tree):
    format first width = format second width

theorem formatKeepsComments ∀ (source output: Text) (width: Nat) (before after: Lexed)
    (formats: format source width = Formatted output)
    (lexedBefore: lex source = Ok before)
    (lexedAfter: lex output = Ok after):
    after.settled.comments = before.settled.comments
```

Notes on them:

- **Totality** is two things. That `format` returns at all is the
  language's: no `Partial`, and `check` accepted every definition. That
  it never gives up for want of fuel or budget is `fuelEnough` (the
  parser) and `renderBudgetEnough` (the engine). With those,
  `formatAnswers` and `formatRefuses` cover every source.
- **Refusals sound** means here what it meant in the toy: `format`
  refuses exactly what `parse` refuses, with its message, and `parse`
  refuses a lexical error, a syntax error or one of the lowering's three
  errors. There is no second grammar to prove the parser against; that
  it refuses what the Rust parser refuses is the harness's gate (the
  1,157 files of §3.5).
- **`formatKeepsComments` compares settled comments.** Rule N trims the
  spaces at a comment's end, so the lexer's own lists differ by that
  much; `lexSettledComments` gives the unsettled form.
- `Degenerate.sw`'s three refuted formatters are not restated: they are
  the toy's file with this `format`.

## 4. The layers, and why each suffices for the one above

```
format's theorems  ←  printParses, tidy's five, parseParsed, parseCarries      (glue)
printParses        ←  printLexes, printedSettle (rules, engine, lexer, rule N), readsBack (parser)
tidy's five        ←  three theorems a pass, seven "keeps the earlier pass" (passes)
parseParsed        ←  parseShaped, parseSettled, parseLexical, parseAccepted    (parser, the joint walk)
```

Every arrow is a proof in `src/Proofs.sw` that `check` accepted, so the
fit below the glue is checked, not argued. In words:

- **Glue.** `format source` is `Formatted (tree.tidy.print width)`. The
  output parses to `tree.tidy` by `printParses`, which needs `Parsed
  tree.tidy` (`parseParsed`, then `tidyParsed`) and no trailing comma
  (`tidyBare`). Same meaning is `tidyKeepsMeaning`. Idempotence is
  `tidyIdempotent`: formatting the output tidies `tree.tidy` again and
  prints the same tree. Comments go round through `parseCarries` on both
  texts and `tidyKeepsComments` between.
- **`printParses`** needs three things: the printed text lexes to the
  tokens the rules wrote (`printLexes`, which is the engine's and the
  rules' "words" and "places" layers and the lexer's read-back of each
  token); rule N takes those leaves to ones that spell the tree
  (`printedSettle`: the toy's `tucksHome` and `settledViews`, plus the
  spelling layer); and the parser reads back what spells a tree
  (`readsBack`).
- **The passes** each give four facts (keeps `meaning`, idempotent,
  keeps `Parsed`, keeps the comments), and each later pass keeps each
  earlier one's fixed point (six statements, plus `mergeKeepsBrackets`,
  which is the P3-before-P4 fact). `tidy`'s five theorems are those
  composed [checked]. The generic lemmas (`traverseKeep`,
  `traverseKeepsMeaning`, `traverseIdempotent`) turn a pass's theorem
  into a fact about its step at one node.
- **`Parsed`** is `Shaped ∧ Settled ∧ Lexical ∧ no refusal`, stated of a
  tree with no source, so a tree a pass built qualifies. The four
  predicates are open: they are written against stage 2's tree.

**Where the fit is not checked.** The open predicates (`Spells`,
`Printed`, `Shaped`, `Settled`, `Lexical`) are prose until stage 2's tree
exists, so `check` can't tell whether `printedSettle`'s `Spells` is the
`Spells` that `readsBack` can use. In the toy that boundary moved twice
(SKETCH.md, "Statements that must change"). The first proof lane on the
parser layer should write `Spells` and `Shaped` out before anything
else.

## 5. Counts per layer

**Stated here** [measured: `grep -c '^theorem'`]:

| Layer | Stated | Open | Statements |
|---|---|---|---|
| Engine | 1 | 1 | `renderBudgetEnough` |
| Lexer and rule N (on stage 1's code) | 7 | 6 | `settledKeepsTokens`, `settledKeepsComments`, `settledIdempotent`, `settledCommasBare`, `settledArrowsBare`, `settledTrimmed`; `lexSettledComments` proved |
| Parser: walk, carry, read-back | 7 | 7 | `parseShaped`, `parseSettled`, `parseLexical`, `parseAccepted`, `parseCarries`, `readsBack`, `fuelEnough` |
| `meaning` and passes | 26 | 26 | 3 generic; P1 4; P2 5; P3 6; P4 7; `tidyFused` |
| Rules and spelling | 4 | 4 | `printLexes`, `printedSettle`, `printWords`, `printWidths` |
| Glue and the must set | 21 | 0 | `printParses`, `tidy`'s 7, `format`'s 8, 5 helpers |
| **All** | **66** | **44** | |

These are each layer's interface: what it hands the layer above. They
are not the lemma count. A sketch at one statement per lemma would be
the proof's skeleton for 250 parser functions and 73 rule functions,
which stage 3's hour doesn't hold; and the predicates those lemmas are
about wait for stage 2's tree. So §7.3 is replaced by the table below:
the interface counts above, and behind each open statement a lemma count
from the toy's measured rate for that kind of work, times a measured
size ratio.

**The toy today, by layer** [measured: `grep -c '^theorem'` by file,
1,729 in `tools/toyfmt/src`]:

| Layer | Toy theorems | Files |
|---|---|---|
| Engine | 302 | `Doc/*` |
| Lexer and rule N | 259 | `LexProofs`, `LexTextProofs`, `TextProofs`, `StringProofs`, `PieceProofs`, `CarryLex` (128); `SettleProofs`, `CarrySettle`, `SettleFine`, `TuckProofs`, `CalmProofs` (131) |
| Parser: walk and carry | 305 | `WalkProofs`, `ShapeProofs`, `StandProofs`, `HeadProofs`, `ParsedProofs` (136); `CarryWalk`, `CarryProofs`, `KeepsComments` (169) |
| Read-back | 150 | `ExpressionProofs`, `BlockProofs`, `FileProofs`, `GroupProofs`, `ItemProofs`, `ParserProofs` |
| Rules | 347 | `WordProofs`, `JoinProofs`, `RuleJoinProofs`, `EventProofs`, `BracketEventProofs`, `TokenEventProofs`, `PlaceProofs`, `LaidProofs` |
| Spelling | 113 | `SpellProofs`, `BlockSpellProofs` |
| `meaning` and passes | 217 | `TraverseProofs` (70), `PassProofs` (49), `BracketProofs` (41), `MergeProofs` (57) |
| Glue and the must set | 36 | `DirectProofs`, `Proofs`, `Degenerate` |

**Size ratios, real over toy** [measured: `grep -c`]: parser functions
250 over 75 (3.3); lexer definitions 52 over 27 (1.9); rule N
definitions 27 over 12 (2.25); rule functions 73 over 36 (2.0), or 7 by
lines; node kinds 98 over 20 constructors (4.9).

**The real formatter** [estimated from the two tables]:

| Layer | Stated here | Lemmas behind them | How |
|---|---|---|---|
| Engine | 1 | 40–80 new; the toy's 302 move with the engine | SW-3452 restates the budget and `fits` lemmas; SW-3416 adds "the cache is the computation" |
| Lexer and rule N | 7 | 540–800 | lexer 128 × 1.9 ≈ 245; rule N 131 × 2.25 ≈ 295; the top of the range is T3's lesson (rule N ran 2.4 times its count) |
| Parser: walk and carry | 5 | 700–1,100 | walk 1.8 a function, carry 1.7 (SW-3641 measured the same) ≈ 875 for 250 functions |
| Read-back | 2 | 450–750 | 2.0 a function ≈ 500 |
| `meaning` and passes | 26 | 250–450 | below |
| Rules | 3 | 700–2,000 | 347 × 2.0 by functions, × 7 by lines; this sketch can't narrow it |
| Spelling | 1 | 450–650 | 113 × 4.9 ≈ 550 |
| Glue and the must set | 21 | about 50 | proved here; plus `Degenerate` and the file loop |
| **All** | **66** | **about 3,200–5,900, middle 4,400** | §7.3 said 3,700–6,500, middle 5,000 |

The passes layer is the one this sketch changes [inferred]. Seven
generic lemmas (the three stated, and `Shaped`, `Settled`, `Lexical` and
the comments each kept by a traversal whose steps keep them), each one
induction over the tree's families and list helpers, about 25 theorems
each at stage 2's size (the toy's six took 70 for a quarter of the
families): 175. Then the steps' own facts: P1 about 10, P2 about 8, P3
about 40, P4 about 85 (the toy's 57, for three kinds of binder list),
the order lemmas about 27. Two things make it smaller than §3.4's
300–600: the real P3 is much narrower than Toy++'s (two slots, not every
expression by precedence), and `meaning` is the traversal, so "keeps
`meaning`" is one generic lemma and four small step facts.

At 80–110 theorems an agent hour that is about 30–70 agent hours, against
§7.3's 40–70. The spread is still the rules layer.

## 6. Where the toy's proofs can be reused

| Layer | Reuse | What changes |
|---|---|---|
| Engine | whole, by moving `Toy.Doc` to `Std.Doc` | SW-3452 (`fits` takes the indent and width; `printBudgetEnough` restated), SW-3416 (cached `forcesBreak`) |
| Glue | whole: `formatRoundTrip`, `formatKeepsMeaning`, `formatIdempotent`, `formatSameTree`, the refusals, `formatKeepsComments`, `tidy`'s theorems are the toy's proof text with names changed [checked: copied, accepted first time] | `Refused` for `ParseError`; the refusal check is inside `parse` |
| Passes | the frame: `TraverseProofs`' generic lemmas, `PassProofs`' composition; `MergeProofs`' argument for P4 | the traversal takes a record of four steps, not a step and a declaration function; P3's `spare` becomes `standsAt` at two slots; P1 is `takes` again |
| Rule N | the method: `Settled` pairwise, `tucksHome`, `stableTokens`, `settledHomed`; `CarrySettle`'s shape | five passes where the toy has two: the bar, `->`, the expression `let` (SW-3750), the stop-early limits |
| Parser carry | the method and its rate (1.7 lemmas and 29 lines a function) | every function is new |
| Read-back | std's `Reads`, `ReadsIn`, `Gives`, the declines toolkit; `After`, `BlockEnds`, `runsExpressionFuel` as patterns | every function is new; many more layout-sensitive constructs than `if` and a block |
| Lexer | `lexCovers`' two-layer shape, which stage 1 kept on purpose (NOTES.md) | text blocks, `${…}`, qualified names, Unicode aliases |
| Rules, spelling | the layer structure (words, joins, events, places, `Laid`, `Seen`) | every rule is new; proved last, after the style settles (§7.4) |

## 7. The riskiest statements

1. **`printedSettle`: rule N at the real size.** The Rust rule keeps a
   trailing comment on a closer or bar that starts its line when moving
   it would pass that token's own-line comments or the line before ends
   with a comment, and turns a bar's kept comment into an own-line
   comment of the next token (`tidy.rs`, clause 1). `Settled` has to say
   that of the tree with no layout: my reading is "a closer has a
   trailing comment only if it has comments above it or the token before
   it has a trailing comment", since either forces the closer onto its
   own line [inferred, not checked against the code case by case]. If a
   case depends on the source's line breaks alone, `printParses` is
   false of it and the tree needs one more flag. This is the layer that
   ran 2.4 times over in the toy.
   **Spike K1 (SW-3825) answered this**: no flag. The reading above was
   wrong in one place ("the code before it ends with a comment, looking
   back past closers, commas and bars", not "the token before it");
   `src/Settled.sw` has the predicate (`homed`), `src/SettledProofs.sw`
   the two statements, and the proof plan's §10 the evidence and the one
   family left out (a trailing comma that starts the closer's line).
2. **`bracketsKeepParsed` and `Expr.standsAt`.** The Rust P3 decides by
   a trial parse of the declaration without the pair (`parens.rs`). The
   tree pass needs a function saying where a type stands unbracketed.
   Two obligations pull on it: the proof (what it lets through, the
   grammar reads back) and the harness (it lets through exactly what the
   trial parse does, including D2307's function type after a row and
   nested pairs). If the grammar's rule for "the type after a row" is
   not a simple class of constructs, the function is a small parser.
3. **`readsBack` for layout.** The toy's two hard parts (D3, D4: a block
   branch of an `if`, and what may follow a block) were its only
   layout-sensitive constructs. The real grammar has blocks, `match`
   arms, handler clauses, `calc` steps, definitions inside a block, a `then`
   that ends its line (SW-3733), all by column. The 2.0 lemmas a
   function is the toy's average, and these are not average.
4. **`fuelEnough`.** True only if no grammar function spends fuel faster
   than it consumes leaves. The toy needed its own induction on the fuel
   (`runsExpressionFuel`) because std's `runsRecursiveWith` says too
   little about the nested parser. Stage 2 should keep one
   `recursiveWith` per recursion and the fuel a function of the leaves
   left. [Spike K4: stage 2's rules read before every call of `self`, so
   `recursiveWith`'s own fuel, the leaves left and one more, is enough.]
5. **`traverseIdempotent`'s hypothesis** (`Settles`), as SKETCH-PLUS
   found: for P4 it says merged groups, traversed again and merged
   again, are unchanged, which needs "merging never uncovers a new
   merge". If it is awkward, state what a finished tree looks like
   instead (a `Bool` function) and prove the traversal reaches it.
6. **`meaning` is trusted, and now narrower than the paper's.** Narrower
   is the safe direction, but `mentions` compares token texts, as
   `merge.rs` does, and a group's split copies the type: a type with a
   comment inside is copied with it. P4 merges no such group, so both
   sides split alike [inferred]. The Opus review of `meaning` (D3643)
   should take `src/Meaning.sw`'s 130 lines and `src/Traverse.sw`
   together.
7. **`Lexical` for text.** A `"""` block by value and `${…}` pieces mean
   the printed text of a `Word` is not the `Word`'s text, and the lexer's
   read-back of it goes through the lexer's own recursion.
8. **The lexer statements held under search, one after a fix.**
   `settledKeepsComments` (order kept, 7,501 cases), `settledIdempotent`
   (4,812), `settledKeepsTokens`, `settledCommasBare`, `settledTrimmed`:
   none found. `settledArrowsBare` was false as first stated: an `->`
   that is the file's last token keeps its trailing comment
   (`arrowsFrom` moves it only when a token follows). Restated for an
   `->` a token follows [searched: 8,501 cases]. No file that parses
   ends in `->`, so nothing depends on it; whether the Rust rule does
   the same was not checked. `settledIdempotent` as first stated (of
   every `Lexed`) is false too: SW-3825's search of 2.4 million short
   token sequences found what the 4,812 cases missed, and it now asks
   for `plain` leaves (`src/Settled.sw`).

## 8. D3617: what becomes droppable, and when

D3617's options were: keep the run-time check always; keep it but skip
the re-parse when the output is the input's text; drop it.

- **The Stitchwort formatter never has the check** (D3620), so the
  question for it is when its output can be trusted without one. As
  stated, every `format` theorem goes through `printParses`, and
  `printParses` needs every layer but the passes. So **"drop" is earned
  only when stage 8 ends**, with the rules and spelling layers, which
  are proved last. Until then the evidence is the harness: byte for byte
  the Rust formatter's output, which the Rust check has passed.
- **What the passes layer alone buys** (26 statements, the first layer
  that can be proved once stage 4 exists): the *tolerant* comparison
  goes. Rust's check compares trees "up to what the passes may change"
  (`same_program.rs`). With `tidyKeepsMeaning` proved, a development
  check for the Stitchwort formatter, if one is wanted during stages
  5–7, is the exact `parse output = Ok tree.tidy`: one re-parse, one
  equality, no tolerance to get wrong.
- **"Skip the re-parse when the output is the input"** needs no theorem:
  the output is then a file that was accepted as written (§7.6).
  `formatIdempotent` is the statement that this case is the common one.
- **For the Rust formatter nothing here is droppable.** These are
  theorems about the Stitchwort program. The Rust check goes when the
  Rust formatter does (Q3).

## 9. Found on the way

- **The paper says 94 node kinds; there are 98** [measured].
- **§3.4's first row overcommits** (item 7 above): a comment-free pair
  is not always forgettable. The table should say "after a row or around
  a parameter's whole type".
- **The real P3 is narrower than Toy++'s P3**, which dropped spare pairs
  around any expression by precedence. The toy rehearsed the harder
  problem.
- **The four passes are one traversal** (`tidyFused`, [searched]: none
  in 2,871 cases, with the two open functions unfolded only as far as
  the search can): the parameters step runs after the types inside are
  stripped, which is the P3-before-P4 order. If proved, the driver walks
  the tree once.
- **`check --counterexamples` works on a sketch**: it found the false
  `settledArrowsBare` in 15 s. Worth a line in the proving guide's
  sketch advice: search every statement about written code before
  counting it.
- **Not done:** the engine's statements are not restated (they are
  `Toy.Doc`'s, proved); `lexCovers` is not stated against stage 1's
  lexemes; the generic "a traversal keeps `Shaped`, `Settled`,
  `Lexical`" lemmas wait for the predicates; `Degenerate` is not
  restated.
