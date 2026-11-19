# Slice 1's grammar, the acceptance theorem, and what the driver still refuses (SW-4120)

Fable, 19 November 2026. Piece A of the path in
[SW-4119's review](SW-4119-slice1-review.md), under D3687 (Matt, 19 Nov
2026): slice 1 is done when the formatter accepts the whole slice 1
grammar and a theorem says so; the grammar is written down exactly; and
anything taken out of it is Matt's decision, with a named later slice.

How claims are marked: **[measured]** a run of mine today; **[checked]**
the checker accepted it; **[source]** read in the code; **[estimated]**
my judgement. Lane estimates start from the review's, which came from
the night of 18 Nov. No estimate or recommendation here rests on how
often a case occurs in the repo.

## Summary

**The problem.** Slice 1's two theorems hold for whatever the driver
accepts, and nothing said what it must accept. The driver refuses six
kinds of source that the design's grammar includes.

**The change.** Three new files in `tools/fmt/src/Fmt`:

- `Grammar1.sw`: the grammar as one definition, `inGrammar1`, with the
  odd cases spelled out and seven closed examples [checked].
- `Accepts1.sw`: the theorem `formatAccepts1`, stated and left open.
- `Tests/MustAccept1.sw`: 144 sources, each tested twice: it is in the
  grammar, and the driver formats it.

**What it shows today [measured].** All 144 sources are in the grammar.
The driver formats 85 and refuses 59. Those 59 tests fail, and stay
failing until the driver accepts them. The test runner has no way to
mark an expected failure, so they are plain failing tests with names
that say what is refused.

**The gap.** Seven things stand between the driver and the theorem. I
recommend lifting all seven in slice 1 and moving nothing out of the
grammar. About 21 to 32 lanes in all [estimated], against the review's
15 to 23: the extra is the two limits the review proposed to leave
(`auto` and the own-line comma) and one obligation the review didn't
list (rule N must not break a parse).

## 1. The grammar

```
File   ::= Def*                               comments and blank lines anywhere
Def    ::= "def" name ":" Expr ":=" Expr      no attributes, `export`, `opaque`, parameters or clauses
Expr   ::= name | numeral
         | "(" Expr ")"
         | "(" Expr ("," Expr)+ [","] ")"     a tuple
         | "[" [Expr ("," Expr)* [","]] "]"   a list, with no `..` spread
         | Expr Expr+                         a call
         | Expr binary Expr                   as the language nests them; comparisons don't chain
         | Expr arrow Expr
         | prefix Expr
name    ::= a name token, plain or qualified, of either case: `x`, `Nat`, `List.map`, `Std.List`
numeral ::= a number token: `12`, `1.5`, `1e3`, `1.5e-13`
binary  ::= || ∨ && ∧ == != ≠ = < <= ≤ > >= ≥ ++ + - * / %
arrow   ::= -> →
prefix  ::= - ! ¬
```

In code (`Fmt.Grammar1`):

```
def inGrammar1 (source: Text): Bool := match lex source with
  | Err _ => False
  | Ok lexed =>
    lexed.leaves.all (leaf => leaf.token.kind.alphabet1)
      && match parseFile lexed with
        | Err _ => False
        | Ok file => file.grammar1
```

A source is in the grammar when the language's lexer reads it, every
token is one of the design's alphabet, the language's parser reads it,
and the tree is built only from the eight forms. `file.grammar1` is a
walk over the tree with `| _ => False` for every other form.

### The choices in it

1. **It is a yes/no function on source text**, so each test and each
   closed example just computes it, and the theorem's condition is one
   equation.
2. **It reads the language's own tree, not the formatter's.** The parse
   is of the lexer's output, before rule N moves any comment. The driver
   parses after rule N. So if rule N ever broke the parse of a source,
   the acceptance theorem would be false; the grammar would not quietly
   shrink to excuse it. The price is a proof that rule N keeps the parse
   (gap item 7).
3. **Nothing about layout, line length or comments is in it.** The walk
   looks at no column, no line start and no comment.
4. **Names and numerals are whatever the lexer reads as a name or a
   number.** There is no test of spelling. That is how qualified names
   and exponents are in: `List.map` is one name token and `1e3` is one
   number token [source: `Syntax/Lexer.sw`, `wordFrom`, `numberTail`].
5. **Operators are whatever the parser built the node with.** A binary
   node is in, whatever its operator. The parser builds binary nodes
   from the 20 operators listed above and no others; `in`, `!in`, `<->`
   and `|>` get node kinds of their own [source: `Syntax/Parser.sw`].
   So there is no operator list in the definition to get wrong or to
   narrow. Each of the 20 has a must-accept test.
6. **It has its own alphabet list** (`Tok.alphabet1`), a copy of the
   design's, separate from the driver's `Tok.within1`. A change to the
   driver's list can't change the grammar. I know of no source whose
   tree is slice 1's with a token outside the alphabet; the list is
   there because the design states one, and it makes the theorem
   cheaper to prove (the parser proofs all assume the alphabet).
7. **It shares no definition with the driver.** `Grammar1.sw` imports
   only the lexer, the parser and the tree types.

### Where the language makes a case odd

Each is stated in the file's header, and the tree decides each one.

| Case | In the grammar? | Why |
|---|---|---|
| `auto` as a value, an argument, a def name, `[auto]`, `[auto, x]`, `[auto x]` | yes | it is a name |
| `[auto Ord]`, `[auto Ord a]` | no | `[`, `auto`, then an upper-case name starts an implicit parameter; the language doesn't read a list here [measured] |
| `Prop`, `Type`, `()`, `_` | no | tokens and tree forms of their own; never in the design |
| `xs.size` | no | a field access; a dotted name is one name only after an upper-case part |
| `a < b < c` | no | a comparison chain, its own form; `(a < b) < c` is in |
| `1_000`, `0xFF` | yes | the language reads two tokens, a numeral and a name, so a call |
| `f -1` and `f - 1` | yes, both | the first is the argument `-1`, the second a subtraction |
| a line inside a value that starts at the same column as the line before | no | the language reads a block of statements, or refuses it (a `,` or closer at an item's column is a parse error in the compiler too [measured]) |
| an empty file, a file of comments only | yes | `Def*` |

The block case is the one place layout matters, and it matters because
it changes which tree the language reads, not because the grammar looks
at it.

### Closed examples [checked]

In `Grammar1.sw`, each by computing: a declaration with comments and a
last comma is in; qualified names, an upper-case def name and an
exponent together are in; a list over five lines with comments inside is
in; `[auto, x]` is in; `[auto Ord]` is out; `Prop` is out; a lambda is
out.

## 2. The acceptance theorem

```
theorem formatAccepts1 ∀ (source: Text)
    (inGrammar: inGrammar1 source = True):
    ∃ (out: Text) => formatWithin1 source = Ok out :=
  ?
```

In `Fmt.Accepts1`, open. It is false of today's driver: each failing
must-accept test is a counterexample. `Fmt.TopStatements` imports it, so
checking the top file reports the open goal.

The statement can't be met by narrowing the driver, since the driver is
on the right-hand side and the condition is the grammar alone. It can be
met only by making the driver accept more, or by changing `Grammar1.sw`,
which is Matt's to decide.

## 3. The must-accept tests

`Fmt/Tests/MustAccept1.sw` [measured: `stitchwort test
Fmt.Tests.MustAccept1`, 288 tests, 229 pass, 59 fail].

| Group | Sources | Accepted today | Refused today |
|---|---|---|---|
| Files (empty, comments only, blank lines, doc comment, CRLF, no last newline) | 6 | 6 | 0 |
| Names | 12 | 2 | 10 |
| Numerals | 6 | 3 | 3 |
| Brackets, tuples, lists | 7 | 7 | 0 |
| Calls | 4 | 4 | 0 |
| Operators (each of the 20, arrows, prefixes, mixes) | 37 | 37 | 0 |
| Layouts (breaks at each kind of place, long declarations) | 23 | 13 | 10 |
| A comment after, and one above, each of the 17 tokens of one declaration | 34 | 10 | 24 |
| More comments (every token at once, inside lists, after last commas, long) | 15 | 3 | 12 |
| **Total** | **144** | **85** | **59** |

All 144 "in the grammar" tests pass. The 59 failing "accepted" tests by
cause, from running the driver's five tests separately on each source
[measured]:

| Cause | Failing tests |
|---|---|
| Doesn't print on one line | 41 |
| Spelling: qualified name 3, exponent 3, `auto` 6 | 12 |
| A last comma that starts its line (`plain1`); 2 of these also fail the one-line test | 5 |
| Upper-case def name | 1 |

The file's header says lanes may add cases but may not remove or weaken
one; only a decision of Matt's does that.

## 4. The gap: what the driver refuses, and what lifting it takes

Models follow D3682: routine proofs to Sonnet, a hard invariant or a
statement that may move to Opus, deciding what to prove to Fable. All
lane counts are [estimated].

| # | Refused | Where | Lanes | Recommendation |
|---|---|---|---|---|
| 1 | A declaration that doesn't print on one line; so also most comments inside a type or value | `oneLine1`, D3685's stage | 9 to 14 | lift in slice 1 |
| 2 | Qualified names, in a type or value and as the def's name | `textSpells1` | 2 to 3 | lift in slice 1 |
| 3 | Exponents | `textSpells1` | half, with 2 | lift in slice 1 |
| 4 | Upper-case def names | `Word.nameWithin1` | 1 | lift in slice 1 |
| 5 | The name `auto` | `textSpells1` | 1 | lift in slice 1 |
| 6 | A last comma that starts its line | `plain1` | 3 to 4 | lift in slice 1, sketch first |
| 7 | (new) nothing proves rule N keeps the parse | between `inGrammar1` and the driver | 2 to 4 | prove in slice 1 |
| 8 | The acceptance proof itself, and the checkpoint | `formatAccepts1` | 3 to 5 | - |

### 1. One line

- **What it is.** After formatting, no token of the type may start a
  line, nor any token of the value after its first. A comment ends its
  line, so this also refuses a comment after or above most tokens: 24 of
  the 34 single-comment tests fail.
- **What changes.** Read-back for a declaration over several lines
  (today `readsBackLineWithin` is for one line); `DeclElements` for
  comments anywhere (today `edgeQuietOneLine1`, edges only); then the
  `oneLine1` test leaves the driver and both top theorems are re-proved.
- **Lanes.** As the review's pieces C to F: one Fable paper lane to
  state multi-line read-back and test the statement on generated files;
  4 to 7 Opus lanes to prove it; 3 to 4 lanes for comments anywhere
  (Opus first, then Sonnet per form); 1 to 2 Opus lanes of glue.
- **Recommendation: lift in slice 1.** It is the bulk of the grammar
  ("comments anywhere", any layout), and it is the machinery every later
  slice stands on.

### 2 and 3. Qualified names and exponents

- **What changes.** The lexer proofs' `Spells` covers names of word
  characters and numbers of digits with a fraction. It needs the dotted
  form and the exponent, with the facts that each lexes back as one
  token of its kind. Then `spelledPlain1` leaves the driver, or becomes
  true of every lexed source.
- **Lanes.** 2 to 3 Sonnet lanes for names, half a lane more for
  exponents. The lexer layer is finished and stable, so this is routine.
- **Recommendation: lift in slice 1.** The design says "a name (plain
  or qualified)" in so many words.

### 4. Upper-case def names

- **What changes.** `parseLexical1` records the def name's token kind
  as lower-case; it needs either kind. `Header.within1` then takes both.
- **Lanes.** 1 Sonnet lane.
- **Recommendation: lift in slice 1.**

### 5. `auto`

- **What changes.** The driver refuses the name everywhere, because a
  printed `[auto Ord …]` would read back as an implicit parameter. But
  no tree in the grammar prints that way: a source with `[`, `auto` and
  an upper-case name never parsed as a list in the first place. So the
  proof needs one more fact about every parsed tree (no list's first
  item starts with `auto` and then an upper-case name), carried the way
  `shaped1` is, and used in the list case of read-back. The spelling
  test on `auto` then goes.
- **Lanes.** 1 Opus lane (a new parser invariant).
- **Recommendation: lift in slice 1.** It is a name; the grammar has no
  reason to treat it otherwise, and the odd case is already outside the
  grammar by the tree.

### 6. A last comma that starts its line

- **What it is.** `[1, 2⏎,]`: a comma on a new line, directly before a
  closer. Rule N parks that comma's comments in a way the "settled"
  facts don't describe, so every rule N and parser theorem from the
  source assumes `plain1`, and the driver tests it.
- **What changes.** The settled facts must describe the parked
  comments, or rule N's handling of this comma must be shown equal to a
  case they do describe. This is also the only case where rule N changes
  a token's layout (the closer is marked as starting the line), so it is
  where item 7 is hardest.
- **Lanes.** 1 Fable paper lane to find the statement, then 2 to 3 Opus
  lanes. Low confidence (SW-3998 was unsure too).
- **Recommendation: lift in slice 1, with the sketch first.** The last
  slice may refuse nothing, so this work is owed whichever slice does
  it, and nothing in a later slice makes it easier. Stop rule: if the
  sketch finds that the settled facts must be restated through every
  layer, bring Matt the choice of moving this case to slice 3 (the
  layout core, which extends rule N).

### 7. Rule N must keep the parse (new)

- **What it is.** The grammar reads the lexer's output; the driver
  parses after rule N (`settledOnce`). For the acceptance theorem,
  "parses, with a slice 1 tree" has to carry from one to the other. It
  is proved that rule N keeps every token (`settledKeepsTokens`), but
  the parser is handed leaves with their comments, and nothing yet says
  its result doesn't depend on them. On all 144 must-accept sources and
  55 other probes the two parses agreed [measured].
- **What changes.** A theorem that the parser's result depends only on
  the tokens, or directly that a slice 1 parse of the lexer's leaves
  gives a slice 1 parse of the settled leaves.
- **Lanes.** 2 to 4, Opus, after a short Fable sketch that can share
  item 6's. Low confidence: it may be a second walk over the parser.
- **Recommendation: prove it in slice 1.** The cheaper alternative is
  to define the grammar by the driver's own parse. I advise against it:
  the theorem would then excuse any source whose parse rule N broke,
  which is the kind of unseen narrowing D3687 is meant to end. The last
  slice needs this fact for the whole language anyway.

### 8. The acceptance proof and the checkpoint

- Once items 1 to 7 are done the driver's remaining tests are the
  alphabet, which the grammar gives directly, and `within1` of the
  tree, which follows from `grammar1` once `within1` no longer narrows
  names. 1 to 2 Opus lanes of glue, with the review's comments
  corollary.
- The Fable checkpoint review, 1 paper lane, then 1 to 3 lanes of
  fixes.

### Not gaps: outside the grammar by the design

`Prop`, `Type`, `()`, `_`, chained comparisons, named arguments, text,
field access, spreads, lambdas, blocks and every other declaration kind
are outside the design's grammar, so the driver is right to refuse them
and no must-accept test covers them. The review suggested bringing
`Prop`, `Type` and `()` in with slice 2; that would be an addition to a
grammar, which is Matt's to decide either way.

### Total and order

21 to 32 lanes [estimated]: the review's 15 to 23, plus `auto` (1), the
own-line comma (3 to 4) and rule N keeping the parse (2 to 4). The
order the review gave still holds: names and numerals (items 2 to 5) on
Sonnet beside the multi-line sketch; items 6 and 7 share one sketch and
can run beside the multi-line proofs; the acceptance proof last.

## Decisions for Matt

1. **The grammar as written here is slice 1's.** In particular: it
   reads the language's tree, not the formatter's; `auto` is in as a
   name; `[auto Ord]`, `Prop`, `Type` and `()` are out. Recommended:
   yes.
2. **Nothing moves out of the grammar**: all seven gap items are lifted
   in slice 1, the own-line comma with a sketch and a stop rule.
   Recommended: yes. The alternative for the own-line comma is slice 3.

## Findings

- The test runner can't mark a test as an expected failure, so the 59
  refused cases are ordinary failures. Any run of `Fmt.Tests` now
  reports them; a verifier or tier that includes fmt's tests needs to
  know, or the runner needs an "expected to fail" mark that turns into
  a failure when the test starts passing.
- `stitchwort check Fmt.TopStatements` in a fresh worktree took 3 min
  28 s [measured], because the check cache for `tools/fmt` isn't cloned
  with the worktree.
- The driver gives one message for three refusals (alphabet, spelling,
  `plain1`), as the review noted; telling which one applied to a source
  took a scratch module.

## Sources

- `tools/fmt/src/Fmt/Grammar1.sw`, `Accepts1.sw`,
  `Tests/MustAccept1.sw` (new); `Slice1.sw`, `Driver1.sw`,
  `TopStatements.sw`; `Syntax/Lexer.sw`, `Parser.sw`, `DeclParser.sw`,
  `Settle.sw`, `SettleProofs.sw`, `ParseWalk.sw`.
- `docs/proposals/self-hosted-fmt-proof-plan.md` §1.1, §1.2;
  `docs/reviews/SW-4119-slice1-review.md`.
- Runs: `stitchwort check` of `Fmt.Grammar1`, `Fmt.Accepts1` and
  `Fmt.TopStatements`; `stitchwort test Fmt.Tests.MustAccept1`;
  `stitchwort run` of a scratch module (deleted) over the 144 sources
  and 55 probes; `stitchwort check` of two scratch files for the
  compiler's reading of a comma at an item's column.
