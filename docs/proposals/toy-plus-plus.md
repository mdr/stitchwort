# Toy++: a sketch

Fable paper lane, SW-3434, 16 November 2026. No builds or tests were run
and no code was changed. Code read at `868637b09` (the toy is tagged
`toy-v1` at `0aeac051d`, D3626).

How claims are marked:

- **[measured]**: counted here with `grep` and `wc` over
  `tools/toyfmt/src`, read from `git log`, or quoted from
  `tools/toyfmt/NOTES.md`, where a lane measured it;
- **[checked]**: read in this repo at the place given;
- **[inferred]**: my reasoning from what I read; nothing was run;
- **[estimated]**: my estimate.

Decided already, and not reopened here: Toy++ comes before the real
formatter (D3625), changes the toy in place (D3626), "the same program"
is a `meaning` function in Stitchwort (D3635), the parser stays on std
`Parse` and Toy++ records a timing (D3636), and the architecture is tidy
passes then a white-space-only printer (D3623,
[after-the-toy-proof.md](after-the-toy-proof.md) §4.3).

## In plain words

**The problem.** The toy's formatter changes only white space, so its
proof is one equation: `parse (print tree) = tree`. The real formatter
drops brackets and commas, merges parameters, adds `∀` and moves
comments. Nobody has proved a formatter of that kind here, and the first
attempt should not be at 94 node kinds.

**The change.** Sprig gets five small additions, one for each kind of
rewrite the real formatter makes (§1). "The same program" becomes a
function, `meaning`, about a page long (§2). The formatter becomes
`parse`, four passes, `print` (§3). Each pass has three theorems, and
the printer keeps the toy's theorem, restated for trees the passes have
tidied.

**What it should do.** About 350 new theorems on the toy's 1,052, and
150 to 250 existing ones edited [estimated, §4]. Eight lanes, about 9.5
agent-hours, a day of elapsed time [estimated, §5]; the toy's first
proof took about 10 hours elapsed for 1,262 theorems [measured, §5]. It
settles the real formatter's theorem statements, shows what a pass costs
per node kind, and records whether a `Parse`-based formatter with passes
stays under 3.0 s per MB (§6).

**The one hard part** is rule N, where a comment belongs. It is the only
addition that changes the printer's proof and not just the passes', and
it is a third of the new work (§3.1, §7).

## 1. Sprig++: what is added

A function before and after formatting, showing all five:

```text
fn area(w: (Int), h: Int,) =         fn area takes (w h: Int) =
  ((w) * h) + offset(                  w * h + offset(w, 1) -- padding
    w, 1 -- padding
  )
```

| # | Addition | Mirrors (fmt-passes.md §1) | What it tests in the proof |
|---|---|---|---|
| A1 | **Rule N**: no new syntax. A trailing comment written after commas and closing brackets belongs to the last token before them; a comma holds no comments | C5, C6, rule N (`crates/fmt/src/tidy.rs`) | The printer's theorem is no longer `parse (print t) = t` on the lexer's raw anchors: the printed comment sits after the closers that fit on its line, which depends on the width, and reading puts it back. The engine writes text in a different order from the document's. Three of the four overnight fuzz bugs were this |
| A2 | **A trailing comma** is accepted in a list, a call's arguments and a parameter list, and dropped | C4, P2 | A pass that deletes one token; the first pass whose result the printer *needs* (it never prints that comma), so the printer's theorem takes a tidy tree |
| A3 | **Redundant brackets** dropped. `Bracketed` is in Sprig already, kept as written today (`Syntax/Tree.sw`, `Expr`) | C2, P3 | A pass that removes a node, with a real side condition: the inner expression must be allowed where the pair stood (precedence), which the Rust formatter checks by re-parsing and the proof must show. Nested pairs go in one run (SW-3482) |
| A4 | **Typed parameter groups**: `(w: Int, h: Int)` merges to `(w h: Int)`. A type is a name, or a type in brackets | C3, P4 | A pass that deletes a run of tokens and regroups a list; "all in one go" for a fold; and a true ordering dependency: `(w: (Int), h: Int)` merges only after its brackets are dropped, so "keeps earlier passes' work" has content |
| A5 | **A cosmetic keyword**, `takes`, between a function's name and its parameters, added when the function has parameters | C1, P1 (`∀`) | A pass that adds a token; `meaning` forgetting an optional thing; a token with no source position |

Each also needs its lexer, parser, rule and read-back lemmas, as any
construct of the toy did; that cost is in §4.

Choices made, with reasons:

- **Type brackets** are the one addition beyond the brief's list. Without
  them all four passes commute and theorem 3 is true for trivial reasons.
  They reuse the bracket rule and cost one node kind. They can be cut if
  stage T2 runs long.
- **`takes`** is a word, not `∀`: a new keyword costs one line in the
  keyword table (`Syntax/Token.sw`, `Keyword.fromWord`), a non-ASCII
  symbol a new lexeme class.
- **An untyped parameter stays one name** (`fn total(order)`), so every
  existing golden still parses. Only typed groups hold several names.
- **Not rehearsed:** text blocks (a lexer matter, as §4.4 of the earlier
  note said); the fallback (it goes); P4's condition that a merged type
  mentions none of the group's names (Sprig has no dependent types); the
  record-update bar; trimming a comment's trailing spaces. Blank lines
  need nothing: the tree already keeps "present or absent", not a count
  (`Spaced.blankBefore`) [checked].

### The tree after the change

```
type TypeExpr =
  | TypeName (name: Text) (comments: Comments)
  | TypeBracketed (open: Comments) (inner: TypeExpr) (close: Comments)

type Named = { name: Text, comments: Comments }

type ParameterGroup =
  | Untyped (parameter: Named)
  --| `w h: Int`: one or more names and the type they share.
  | Typed (names: NonEmptyList Named) (colon: Comments) (type: TypeExpr)
```

`ListLiteral` and `Call` gain `trailingComma: Bool`; `Function` gains
`takes: Option Comments` and `trailingComma: Bool`, and its parameters
become `List ParameterGroup`. **`Item` and `Parameter.comma` go**: under
rule N a comma holds no comments, so a list's items are `List Expr`. That
deletes `Shaped`'s clause "no last parameter or item keeps a comma's
comments" and its lemmas (`BareLastItem`, `Syntax/ShapeProofs.sw:33-48`)
[checked].

## 2. `meaning`

`meaning` gives the tree in *plain form*: the same tree type, with each
freedom set to one fixed spelling. Two files are the same program when
their plain forms are equal. The result is wrapped so that a plain tree
can't be printed by mistake (it need not have the parser's shape: its
grouping is in the tree, not in brackets).

```
--| What formatting must keep.
type Meaning = { plain: SourceFile }

def SourceFile.meaning (file: SourceFile): Meaning :=
  { plain = { declarations = plainDeclarations file.declarations } }

def Comments.isNone (comments: Comments): Bool := comments.above.isEmpty && comments.after.isNone

def Expr.plain: Expr → Expr
  -- A pair that holds no comment is forgotten: the tree's shape says how
  -- the expression groups. A pair that holds one is kept, with it.
  | Bracketed open inner close =>
    if open.isNone && close.isNone then inner.plain else Bracketed open inner.plain close
  | ListLiteral open items _ close => ListLiteral open (plainItems items) False close
  | Call callee open arguments _ close => Call callee.plain open (plainItems arguments) False close
  | Field target dot name nameComments => Field target.plain dot name nameComments
  | Negate minus operand => Negate minus operand.plain
  | Binary operator sign left right => Binary operator sign left.plain right.plain
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    If ifComments condition.plain thenComments whenTrue.plain elseComments whenFalse.plain
  | leaf => leaf

def TypeExpr.plain: TypeExpr → TypeExpr
  | TypeBracketed open inner close =>
    if open.isNone && close.isNone then inner.plain else TypeBracketed open inner.plain close
  | name => name

--| The type's name alone: no brackets, no comments.
def TypeExpr.bare: TypeExpr → TypeExpr
  | TypeBracketed _ inner _ => inner.bare
  | TypeName name _ => TypeName name Comments.none

-- One group for each name. The group's own `:` and type, with their
-- comments, stay with its last name; the names before it get the bare type.
def ParameterGroup.plain: ParameterGroup → List ParameterGroup
  | Untyped parameter => [Untyped parameter]
  | Typed names colon type => split names.toList colon type.plain

def split (names: List Named) (colon: Comments) (type: TypeExpr): List ParameterGroup := match names with
  | [] => []
  | [last] => [Typed [last] colon type]
  | [first, ..rest] => [Typed [first] Comments.none type.bare, ..split rest colon type]

def Declaration.plain: Declaration → Declaration
  | Function fnComments name nameComments takes open groups _ close equals body =>
    Function fnComments name nameComments (Some (takes.getOrElse Comments.none)) open (plainGroups groups) False close
      equals body.plain
  | Value letComments name nameComments equals body => Value letComments name nameComments equals body.plain
  | note => note
```

`plainItems`, `plainGroups` (which concatenates), `Body.plain`,
`Statement.plain` and `plainDeclarations` are the list helpers and
structural cases, one line each, as the toy's rules already need
(friction B2). `[last]` stands for a one-item `NonEmptyList`. About 60
lines in all [estimated].

How each freedom disappears:

| Freedom | In `plain` |
|---|---|
| Redundant brackets | a pair with no comment is replaced by what it holds, for expressions and types |
| Parameter grouping | every group is split to one name each; `(w h: Int)` and `(w: Int, h: Int)` both become `w: Int`, `h: Int` |
| The optional `takes` | absent becomes "present with no comments" |
| A trailing comma | the flag is set to `False` |
| Which side of a closer or comma a comment was written | nothing to do: `parse` applies rule N, so the tree already holds each comment at N's anchor, and `plain` keeps every `Comments` field as it is |
| Blank-line counts | nothing to do: the tree holds present or absent |

What it does not forget: every name, number and string as written, every
operator, the order of everything, every comment's text and the token it
belongs to, every kept blank line, and any bracket pair, `takes` or
group separator that carries a comment. That last part is what makes
"a pair that touches a comment stays" a consequence of the theorem and
not a rule someone must remember: a pass that dropped such a pair would
change `meaning`.

**The cross-check has no Sprig counterpart.** D3635's check that
`meaning` forgets nothing the compiler sees is the fuzzer's Rust hash
comparison. Sprig has no compiler. Toy++ can rehearse the definition and
the proofs, and extend the disturber (`Fmt/Tests/Disturb.sw`) to make
the five changes at random (wrap an operand in brackets, split a group,
add a trailing comma, drop `takes`, move a comment across a closer) and
test `format (disturb s) = format s` on the goldens. That tests the
passes against `meaning`'s intent; it does not test `meaning` against a
second definition. See Q2.

## 3. The formatter and its theorems

```
def parse (source: Text): Result SourceFile Text     -- lex, then rule N on the tokens, then the parser

def SourceFile.tidy (file: SourceFile): SourceFile :=
  file.withTakes.withoutTrailingCommas.withoutSpareBrackets.withMergedParameters

def format (source: Text) (width: Nat): FormatResult := match parse source with
  | Err message => ParseError message
  | Ok tree => Formatted (tree.tidy.print width)
```

### 3.1 Rule N: a reading rule, not a pass

As in the Rust formatter (fmt-passes.md §2), N can't be a tree pass run
once: plain text can't express its result, so it runs every time tokens
are read. `settle: List (Parse.Located Token) → List (Parse.Located
Token)` sits between the lexer and the parser and follows
`tidy.rs:19-28` [checked]:

1. a trailing comment on a comma or closing bracket moves to the nearest
   token before it that is neither. It stops early, on a closer that
   starts its line, if going further would pass that closer's own-line
   comments or land on a token that already has a trailing comment;
2. a comma's own-line comments, and the trailing comment of a comma that
   starts its line, become own-line comments of the next token.

The parser is unchanged by it. Three other things change:

- **The engine.** Today text that follows a waiting trailing comment
  starts a new line (`Doc/Print.sw:149-154`) [checked], so `[a, b -- c]`
  prints with `]` on a line of its own (`closeAfter`, `Fmt/Rules.sw`).
  Sprig++ prints `[a, b] -- c` when it fits, as the Rust engine does
  (S39). `Doc` gets one leaf, `Closing (text: Text)`, for `)`, `]` and
  `,`: written before a waiting comment, and measured that way by
  `fitsFrom`. It has to be the engine and not the rules, because whether
  the closer shares the comment's line is the engine's choice.
- **The engine's theory.** `Words` says every reading writes the
  document's words in order. With `Closing` a comment is written after
  the closers that follow it. The statement becomes: in order, except
  that a trailing comment follows the `Closing` words written on its
  line.
- **One new lemma where printed tokens meet the tree.** Today the
  printed tokens' views are the views of the tree's events
  (`parsedPrintPlaced`, `Fmt/DirectProofs.sw:22`). Now the lexer puts a
  printed comment on the last closer of its line, and the lemma is that
  `settle` puts it back:

  ```
  theorem settledViews ∀ (file: SourceFile) (width: Nat) (parsed: Parsed file) (bare: NoTrailingCommas file):
      ∃ (events: List Event) (tokens: List (Parse.Located Token)) (endTrivia: List Trivia) =>
        FileEvents file events
          ∧ (lex (file.print width)).map settleLexed = Ok { tokens = tokens.reverse, endTrivia = endTrivia.reverse, .. }
          ∧ tokens.map viewOf = (viewsOf events).views
          ∧ endTrivia = (viewsOf events).pending
          ∧ Descending (tokens.map (token => token.offset))
  ```

  (The shape only: `settleLexed` stands for `settle` applied to the
  lexer's tokens, and T0 fixes the exact form. That `∃` takes several
  binders, and that a proof of one can be written as a tuple, was
  checked with the release CLI on a scratch file.) Everything after it
  (spelling, read-back) sees the tree's own views
  and keeps its shape [inferred: `spellsFile` and `runsFileSpelled`
  already take views and predicates, not a source,
  `Fmt/BlockSpellProofs.sw:2722`, `Syntax/FileProofs.sw:290`, checked].

**What the printer needs of a tree: `Settled`.** A tree that holds a
trailing comment on a closer that N would have moved prints the same
text as the settled tree, so it can't read back to itself. `Settled`
says: a closer has a trailing comment only if it has own-line comments
above it or the expression before it ends in a comment
(`Expr.endsWithComment`, which the rules already have). In both cases
the rules put the closer on its own line already (`closer`,
`closeAfter`) [checked], so N leaves the printed comment where it is.

**The open proof question: why is a parsed tree `Settled`?** The first
clause is a fact about one token, and joins the walk as `Lexical` did
(`Parse.Invariant.every`). The second relates a closer to the token
*before* it, which the parser has already read. Two ways, to be chosen
in the sketch stage:

- (A) a small tree function that re-homes such a comment where the
  parser builds a closer, as `Expr.withoutFirstAbove` clears first
  comments today (`Syntax/Parser.sw:347`; that move replaced 45 to 55
  walk lemmas with 15). It never fires on settled tokens, which we would
  not prove. About 15 lemmas [estimated];
- (B) one more conjunct in the joint walk: "the value ends in a comment
  exactly when the last token read has one". About 45 walk lemmas edited
  and 20 value lemmas added [estimated].

I'd try (A) first. The real formatter faces the same choice at 234
parser functions, which is why it should be met here.

### 3.2 The four passes

Each is a function on trees. A tree is *tidy for a pass* when the pass
leaves it alone: `Tidy p file` is `p file = file`. So there is no
second definition per pass to keep in step, and tidiness is decidable
with the tree's derived `==`.

| Pass | Does | Leaves alone |
|---|---|---|
| P1 `withTakes` | `takes = None` becomes `Some Comments.none` on a function with at least one parameter | a function with none, whatever was written |
| P2 `withoutTrailingCommas` | every `trailingComma` becomes `False` | nothing: after N a comma has no comments to lose |
| P3 `withoutSpareBrackets` | bottom-up, replaces `Bracketed open inner close` by `inner` when neither bracket holds a comment, `inner` has no own-line comment above its first token, and `inner` is allowed where the pair stood; always for a type's comment-free pair | a pair holding a comment; a pair whose content needs it |
| P4 `withMergedParameters` | folds a function's groups once, right to left: `Typed a none (TypeName n none)` followed by `Typed b colon type` with `type.bare = TypeName n none` becomes `Typed (a ++ b) colon type` | untyped parameters; a group whose `:` or type holds a comment |

"Allowed where the pair stood" uses functions the toy has
(`Syntax/ShapeProofs.sw:52-75`) [checked]: a callee or a field's target
must be `isPostfix`; the operand of `-` must be `isOperand`; a left
operand of a level-`n` operator needs `chainLevel ≥ n`, a right operand
`chainLevel > n`; a body, an item, a condition and a bracket's content
take anything. This replaces the Rust formatter's "drop it, re-parse,
compare" with a condition the proof can use.

The order is P1, P2, P3, P4, as in fmt-passes.md §3.1. The only
dependency is P3 before P4.

**The three theorems, for each pass `p`** (shown for P3):

```
-- 1. Keeps the meaning. No hypothesis: the pass is right on every tree.
theorem bracketsKeepMeaning ∀ (file: SourceFile): file.withoutSpareBrackets.meaning = file.meaning

-- 2. Finishes in one run.
theorem bracketsIdempotent ∀ (file: SourceFile):
    file.withoutSpareBrackets.withoutSpareBrackets = file.withoutSpareBrackets

-- 3. Keeps what came before: the parser's guarantees and rule N's, and
--    each earlier pass's tidiness.
theorem bracketsKeepParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.withoutSpareBrackets

theorem bracketsKeepTakes ∀ (file: SourceFile) (tidy: file.withTakes = file):
    file.withoutSpareBrackets.withTakes = file.withoutSpareBrackets

theorem bracketsKeepCommas ∀ (file: SourceFile) (tidy: file.withoutTrailingCommas = file):
    file.withoutSpareBrackets.withoutTrailingCommas = file.withoutSpareBrackets
```

with

```
--| What a pass and the printer may assume of a tree, and must keep.
def Parsed (file: SourceFile): Prop := ShapedFile file ∧ LexicalFile file ∧ HeadedFile file ∧ SettledFile file

theorem parseParsed ∀ (source: Text) (file: SourceFile) (parsed: parse source = Ok file): Parsed file
```

`bracketsKeepParsed` is where the content is: keeping `Shaped` is the
precedence argument, and keeping `Headed` is why the pass leaves a pair
whose content starts with an own-line comment. Four passes give 4
meaning theorems, 4 idempotence theorems, 4 `…KeepParsed` and 6 "keeps
the earlier pass" theorems; most of the last are true because the later
pass doesn't touch what the earlier one reads.

### 3.3 The printer and the whole

```
-- 4. The toy's theorem, for a tree and not for a source.
theorem printParses ∀ (file: SourceFile) (width: Nat)
    (parsed: Parsed file) (bare: file.withoutTrailingCommas = file):
    parse (file.print width) = Ok file

theorem tidyKeepsMeaning ∀ (file: SourceFile): file.tidy.meaning = file.meaning
theorem tidyParsed ∀ (file: SourceFile) (parsed: Parsed file): Parsed file.tidy
theorem tidyIdempotent ∀ (file: SourceFile): file.tidy.tidy = file.tidy

-- 5. The whole.
theorem formatAnswers ∀ (source: Text) (width: Nat) (tree: SourceFile) (parsed: parse source = Ok tree):
    format source width = Formatted (tree.tidy.print width)

theorem formatKeepsMeaning ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    ∃ (before after: SourceFile) =>
      parse source = Ok before ∧ parse output = Ok after ∧ after.meaning = before.meaning

theorem formatIdempotent ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    format output width = Formatted output
```

Two things to notice.

- **The printer needs only N and P2.** It prints brackets, groups and
  `takes` as the tree has them, so P1, P3 and P4 are not hypotheses of
  `printParses`: they matter to idempotence alone (fmt-passes.md says
  the same of the Rust printer, "printer may assume: nothing new").
- **`printParses` no longer mentions a source.** Today it takes `parse
  source = Ok file` (`Fmt/DirectProofs.sw:51`), which a tidied tree
  doesn't have. The lemmas under it already take the predicates; only
  the `parsed…` wrappers (`parsedPrintTokens`, `parsedPrintEvents`,
  `parsedPrintPlaced`) take a source [checked], so restating is peeling
  those. That can be done on today's toy, before anything else (stage
  T1).

The glue is as short as today's (`DirectProofs.sw` is 95 lines):
`formatKeepsMeaning` is `parseParsed`, `tidyParsed`, `printParses` and
`tidyKeepsMeaning`; `formatIdempotent` adds `tidyIdempotent`, since the
output parses to `tree.tidy`, which `tidy` leaves alone.

### 3.4 One experiment inside the passes: a shared traversal

P2, P3 and `plain` all walk every expression. Written separately, each
pass theorem is an induction over the tree's eight mutually defined
parts (expression, items, statement, statements, body, declaration,
declarations, file), so cost goes as passes × theorems × parts. At 94
kinds and six passes that product is the real formatter's risk. Stage
T5 should write P3 through one `Expr.rewrite (step: Expr → Expr)` with
its lemmas once ("if `step` keeps P at a node, `rewrite step` keeps P"),
and report whether Stitchwort's termination checker and `Shaped`'s
position-dependence allow it. If it works, P2 and `plain` move onto it.

## 4. What carries over, what is restated, what goes

The toy today, by layer [measured: `grep -c '^theorem'` and `wc -l` per
file; 1,052 theorems, 23,626 proof-file lines, 1,676 program lines]:

| Layer | Theorems now | Toy++ | New [estimated] |
|---|---|---|---|
| Engine (`Doc/*`) | 224 | carries over; `Closing` adds an arm to each invariant's induction, and `Words`' order statement is restated | 15-25, about 40 edited |
| Lexer | 138 | carries over; `:` and `takes` | 10-15 |
| Rules: words, joins, events, places | 319 | carries over for existing constructs; commas become plain text; four new rule functions (group, type, `takes`, the parameter list); `settledViews` and `settle`'s lemmas | 30-45 for rules, 30-50 for N |
| The walk | 118 | carries over (std `Parse.Gives`); the last-comma clause goes; 6-8 new parser functions; `Settled` | 10-15, plus §3.1's (A) or (B) |
| Read-back | 132 | carries over; new functions | 20-30 |
| Spelling | 107 | carries over; three new node kinds | 15-25 |
| Glue | 14 | `printParses` and `format`'s three restated | 10 |
| Passes and `meaning` | 9 (`…Cleared`) | new: 18 named theorems of §3.2, each a mutual induction of up to eight parts | 130-220 |
| **All** | **1,052** | | **280-450, middle about 350** |

- **Unchanged:** the engine's readings, "tokens don't merge", rule
  triples and the whole read-back method. Nothing in Toy++ needs a new
  idea there except `Closing`.
- **Edited, not new:** every lemma that matches on `Function`, `Call` or
  `ListLiteral` (their fields change) or on `Item`: 150 to 250 theorems
  [estimated], mechanical, found by `E-NONEXHAUSTIVE` and arity errors
  as friction 67 describes.
- **Deleted:** the comma-comment lemmas (10-20), the three `parsed…`
  wrappers.
- **End size:** about 1,350 to 1,450 theorems [estimated]. The earlier
  note said 200-350 new; this is higher because N is done in the engine
  and typed groups bring a second bracket kind.

**Lines.** The toy averages 22.5 proof-file lines a theorem [measured].
At that rate 350 theorems are about 7,900 lines. Proof tuples (built)
take 3-5% off and remove the bracket-counting errors
(proof-tuples.md §7) [its estimate]: about 7,500. `simp` stage 1 is
estimated at 22-29% of proof text on the engine slice
(simp-revisited.md) [its estimate], and the pass theorems are its best
case (unfold, rewrite, both sides agree): with it, 6,000 to 6,800
[estimated]. New proofs should be written with tuples from the first
lane. SW-3519 (the tuple sweep of the existing toy) edits every proof
file, so it should run before T1 or after T7, not between.

## 5. Stages

Each leaves the toy checking. Times are agent time. For scale: the
toy's direct proof (SW-3418) ran from 14:35 on 15 November to 00:30 on
the 16th, about 10 hours elapsed, 148 commits, 1,262 theorems
[measured, `git log --grep SW-3418`]; lanes proved about 80 theorems
each in 25-50 minutes (after-the-toy-proof.md §1).

| Stage | What | Model | Est. | `simp` |
|---|---|---|---|---|
| T0 | **Sketch in code**, as `SKETCH.md` did for the toy (D3620): the new tree, `settle`, `meaning`, the four passes and every theorem of §3 stated in a side project with open goals, checked for fit. Decides (A) or (B) for `Settled`, and whether §3.4's traversal type-checks | Fable | 75 min | before |
| T1 | **`printParses` over predicates** on today's toy: `Parsed`, `parseParsed`, the wrappers peeled. No syntax change | Sonnet | 30 min | before |
| T2 | **The syntax**, printed as written: `:`, `takes`, types, groups; lexer, parser, rules, goldens; the walk, read-back, spelling and rule lemmas for them. Two lanes on one branch (parser side, then printer side), merged when `printParses` checks again. About 100 theorems | Opus | 2 × 70 min | before |
| T3 | **Rule N**: `Closing` in the engine and its theory; `settle`; commas lose their comments (`Item` goes); `Settled`; `settledViews`. Two lanes on one branch. About 100 theorems, the least certain | Fable or Opus | 2 × 90 min | engine half is better after stage 1; don't wait more than a day |
| T4 | **The pass frame**: `meaning`, `tidy`, `format` and §3.3's theorems, with P1 and P2 (the parser accepts a trailing comma here, with its flag). About 60 theorems | Opus | 75 min | better after stage 1 |
| T5 | **P3, brackets**: the precedence argument and §3.4's traversal experiment. About 70 theorems | Opus | 90 min | better after stage 1 |
| T6 | **P4, merging**, and the P3-before-P4 theorems. About 25 theorems | Sonnet | 45 min | better after stage 1 |
| T7 | **Close**: the timing (§6), the disturber's five new changes, NOTES with friction and counts by layer, tag `toy-v2` | Sonnet | 30 min | either |

About 9.5 agent-hours [estimated], eight stages, ten lanes. T0 to T2
need nothing from `simp` (structure, positions and `Gives` lemmas, where
tuples help and `simp` doesn't). T3's engine half and T4 to T6 are
equational and are what `simp` stage 1 was measured on; `simp`'s stage 0
is in progress (SW-3529, SW-3530) and stage 1 is estimated at 5 h
(simp-revisited.md §8) [checked on the board: no stage 1 ticket yet].
If stage 1 hasn't landed when T2 merges, start T3 anyway: the cost is
about a quarter more proof text in those stages [estimated], and the
converted proofs become `simp` stage 4's test set.

T3 comes before the passes because it is the riskiest and because it
simplifies the tree the passes walk (no comma comments). T0 and T1 can
run at once; T2 to T6 edit the same files and run one after another.

The earlier note's three structural experiments (§3.4 (a) values that
can't be ill-formed, (b) documents whose leaves are tokens, (c) layout
as a pass) are not in these stages. (b) would replace the layer
`settledViews` lives in, so T0 should say whether to do (b) first; my
expectation is no, and that (b) is its own lane after `toy-v2`.

## 6. The timing for D3636

**What is measured.** The whole format (lex, `settle`, parse, the four
passes, print) of a generated file of about 1 MB, built natively,
`Toy.Timing.main` extended so the file has Sprig++'s constructs at
plausible rates: typed groups on every function, a spare bracket pair
and a trailing comma every few lines, a comment before a closer every
twenty. Median of three runs at load under 5, with instruction counts,
which NOTES found steadier. Phases by differencing, as now (there is no
clock in `IO`). Reported as seconds per MB, with no check at run time.

**The baseline.** 1.91 s for 933 KB, 2.05 s/MB, at load 3.5 [measured,
NOTES "Speed (SW-3383)"]; 2.39 s (2.56 s/MB) at load 50 [measured,
NOTES stage D]. The 2.2 s/MB quoted in D3636's discussion lies between
the two; I didn't find that exact figure in NOTES.

**The bar.** Pass: **3.0 s/MB or less** at load under 5. That is the
rate at which the repository's 6.5 MB takes 19.5 s against the 20 s
target (6.5 MB from NOTES stage D, the target from
after-the-toy-proof.md §4.6). It allows the passes and
N about 0.9 s/MB over the baseline; I expect 0.3 to 0.5 (five linear
walks that rebuild the tree; printing, which builds a document as large,
is 0.3 s/MB) [estimated]. Also recorded: the passes' and `settle`'s
share of the total, to stay under a quarter.

**What it does not show.** The real grammar has 234 parser functions to
Sprig++'s roughly 72, so the real rate per MB will be higher than
Toy++'s. The measurement confirms that passes and N are cheap and that
`Parse` is not what breaks the target at this size; it does not replace
a timing of the real parser at stage 0. If it fails: fuse the passes
into one walk, and file what the profile shows as `Parse` speed work.

This is one small run, not the benchmark suite; T7's brief should name
it so the lane doesn't need to ask.

## 7. Risks

- **Rule N's proof (T3).** Three unknowns in one stage: the engine's
  order theorem restated, `settledViews`, and `Settled` for parsed
  trees. T0 states all three before anyone proves anything. If T3 hits
  its stop rule, the fallback is to land `Closing` and `settle` with
  `Settled`'s neighbour clause by route (A), which is the cheap one.
- **Passes × theorems × node kinds.** If §3.4's shared traversal doesn't
  work in Stitchwort, the real formatter's pass layer is nearer 6 × 5 ×
  94 arms than the 150-300 theorems estimated for it. Toy++ finds out at
  17 kinds; that is its second most useful result after N.
- **`meaning` is trusted, and Toy++ can't cross-check it** (§2). A wrong
  `plain` that forgets too much would make every pass theorem easier,
  not harder, so the proofs can't catch it. The page is short enough to
  review by eye, and should get an Opus review when T4 lands.
- **`Shaped` was written for the parser's output.** P3 needs "allowed
  here" as a function and `Shaped` as its consequence. If they don't
  line up, `Shaped` is restated, which touches the walk [inferred from
  `ShapeProofs.sw`'s header; T0 checks].
- **Churn against other toy lanes.** T2 and T3 edit most proof files. The
  tuple sweep (SW-3519), the declines toolkit (SW-3507) and the
  "may follow" table (SW-3511) touch the same files and should run
  before T1 or after T7.
- **`simp` slips or is too strict.** Covered in §5: nothing blocks on it.
- **Check time.** A third more theorems; the toy's own check time isn't
  in NOTES as one figure, so T7 should record it before and after.

## 8. Questions for Matt

Two. The orchestrator numbers them.

**Q1. Is `meaning` the same tree in plain form, or a second tree type?**
[rec: the same tree, wrapped]

*The problem.* `meaning` is the one definition the theorems rest on that
nothing proves. It should be short enough to read and hard to get wrong.

*The change.* §2 writes it as "the tree with each freedom set to one
spelling", about 60 lines, reusing the tree's types and its derived
`==`. The alternative is a second set of types that can't hold the
freedoms at all (no trailing-comma flag, parameters already one name
each), with a function between them.

*What it should do.* The same tree keeps the trusted text to the cases
that change (about 15 lines of substance here) and scales to 94 kinds
without writing the tree twice. The second type shows what is forgotten
in its definition, but doubles the tree, and still can't remove
`Bracketed`, since a pair holding a comment must be kept. Toy++ sets the
pattern the real formatter copies.

**Q2. Should Sprig get a small evaluator, so that `meaning` is checked
against something?** [rec: no]

*The problem.* For Stitchwort, the fuzzer's hash comparison checks that
`meaning` forgets nothing the compiler sees. Sprig has no compiler, so
Toy++ rehearses the proofs but not that check.

*The change.* Give Sprig an evaluator (about 60 lines) and prove that
files with equal `meaning` evaluate equally: about one lane and 40
theorems [estimated].

*What it should do.* It would be a small model of "the lowering is in
Stitchwort too", which D3635 put off until the compiler moves. It
teaches nothing the real formatter needs soon, and the real cross-check
is already built in Rust. The extended disturber (§2) is the cheaper
stand-in.

Not Matt's, noted for the orchestrator: the spelling `takes`; whether
type brackets stay in scope if T2 runs long (§1); (A) or (B) for
`Settled` (§3.1, decided by T0); the 3.0 s/MB bar (§6); sequencing
against SW-3519, SW-3507 and SW-3511 (§7); which model takes T3.
