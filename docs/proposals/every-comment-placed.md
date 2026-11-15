# Every comment has a place

**Status:** proposed, 15 November 2026 (SW-3446, for D3618). Paper lane:
nothing is built. The probes were throwaway files in the lane's scratchpad,
run with the main checkout's release binary (built 16:30 today) and, for the
toy, `stitchwort run Toy.Fmt.main`. One question for Matt,
[D3619](#d3619-the-principle-and-its-layout-cost).

**Update, SW-3447 (lane R, `stitchwort fmt`): built**, D3619 adopted. One
difference from §2 and §3: when code would follow a trailing comment, the
engine measures the rest of the construct from the line that code goes on,
instead of breaking the construct. So most awkward positions keep the
author's layout rather than the shapes worked by hand in §3 (`x + -- c`
then `x` below, not `+` alone on its line). The 24 probes and their
outputs are the golden `crates/fmt/tests/it/golden/comments-anywhere`;
formatter-style.md S40 states the rule as built.

Claims are marked **[measured]** (a run today, one each), **[source]** (read
in the code named) or **[estimated]**. Outputs marked *proposed* are what
the rules below give, worked by hand; nothing prints them yet.

## In plain words

**The problem.** Both formatters have a hole. When a comment sits somewhere
no printing rule expects (after `:=`, after an operator, on its own line
before `then`), they give up on the whole declaration and leave it exactly
as written. `stitchwort fmt` keeps 11 of 24 awkward positions that way, the
toy formatter 17 of 20 [measured]. The repo has none today only because a
test holds the count at 0, so authors move such comments by hand. In the
toy, this fallback is also the one piece the direct correctness proof
(SW-3418) can't cover: a declaration printed as its source text needs the
whole lexer and parser re-run on it.

**The change.** One rule, the same in both formatters: *a comment stays
next to the token it was written next to, and the formatter breaks the line
wherever that needs.* An own-line comment stays on its own line just above
the token after it; a trailing comment stays at the end of the line after
the token before it, and the next code goes on a new line. Where the house
layout already breaks there, nothing changes; where it doesn't, the
formatter adds a break, indented like the construct's other continuation
lines. One special case, for comments before a closing bracket.

**What it should do.** No declaration is ever left as written because of a
comment: formatting becomes a total function. The 11 + 17 probe positions
all format [proposed]. The repo's output doesn't change (no declaration
there has such a comment today [measured]). The price is a few unusual
layouts in rare spots, such as an operator alone on its line with its
comment. In the toy, the `AsWritten` node goes, and with it the proof's
only case that needs a re-parse, so `format` never re-parses. Cost: two
lanes that can run side by side, about an hour each in agent time
[estimated from past actuals, below].

## 1. What happens today

### 1.1 The repo

`stitchwort dev fmt-tree --verbose` over each top-level folder, and
`stitchwort fmt --check` (which now names each declaration it keeps as
written) over each [measured]:

| Folder | Files | Declarations | Left as written |
|---|---|---|---|
| aoc | 633 | 10,020 | 0 |
| crates | 216 | 6,213 | 0 |
| examples | 1,973 (111 don't parse) | 12,277 | 0 |
| web | 723 | 11,368 | 0 |
| docs | 162 (3 don't parse) | 1,520 | 0 |
| tools | 33 | 701 | 0 |
| games | 29 | 524 | 0 |
| sf | 15 | 442 | 0 |
| bench, dev, book | 51 | 339 | 0 |
| **Total** | 3,835 | 43,404 | **0** |

Zero is by construction: S40 says the repo-wide count is tested to be 0.
So the cost today is not unformatted code in the repo; it is a formatter
that is partial, a rule authors have to know, and a proof gap in the toy.

### 1.2 Awkward positions, `stitchwort fmt`

One probe file per position [measured]. "Kept" means left as written, with
the reason the formatter gives; the attempted print comes from
`STITCHWORT_FMT_TREE_DEBUG=1`.

| # | Position | Today | Why |
|---|---|---|---|
| p01 | trailing, after a definition's `:=` | kept (comments) | the one-line body option printed `:= x + 1 -- c`, moving the comment onto `1` |
| p05 | trailing, after `(` | kept (comments) | printed `(x) -- c` |
| p06 | trailing, after a binary operator | kept (comments) | breaks go before operators: printed `+ x -- c` |
| p07 | own-line, between a function and its argument | kept (no rule places) | the forced line started at column 2, where it would be a new statement |
| p09 | trailing, after a header's last `)` | kept (comments) | printed `(x: Nat): -- c`, moving it onto `:` |
| p11 | own-line, before a closing `]` | kept (no rule places) | the comment and `]` landed at column 0 |
| p12 | trailing, after `let y :=` | kept (comments) | printed `let y := x -- c` |
| p13 | trailing, after an arm's `=>` | kept (comments) | printed `=> n -- c` |
| p14 | own-line, before `:=` | kept (no rule places) | column 0 |
| p17 | own-line, before `then` and before `else` | kept (no rule places) | `then` at the `if`'s column |
| p24 | trailing, after `|>` | kept (comments) | printed `|> Nat.succ -- c` |
| p02, p03, p04, p08, p10, p15, p16, p18–p23, and p13's `with` | above the body; after `then`/`else`; after `[`; after the name; after `:`; after `with`; after `type … =`; before an operator; after `fun … =>`; after an operand; after a theorem's `:`; after the function; before `)`; own-line between parameters | formatted | |

So 11 of 24 kept. Two causes, both in how the printer places a comment the
rules didn't plan for [source: `crates/fmt/src/printer/engine.rs`,
`rules.rs`]:

- **A trailing comment is a `LineSuffix`** that waits for the end of the
  line. When the rules put more code on that line (a one-line option, a
  fixed space, a break before an operator), the comment drifts past it and
  lands on another token; the comment check catches it ("comments").
- **An own-line comment is preceded by `LineStart`**, which starts a line
  if the rules didn't. It starts it at whatever indentation is in force,
  which in a layout that never meant to break there can be the statement's
  own column (a new statement) or 0. So the engine counts it (S40, "comment
  no rule places") and the declaration is refused.

Every token's comments are already emitted next to it (`Rules::leaf`), so
the rules don't lose comments; the engine just has no safe place for the
break. That is what the change supplies.

### 1.3 Awkward positions, the toy

Twenty Sprig probes at width 40, `toyfmt` [measured]: 17 kept as written.
Formatted: a trailing comment after a comma (the item's), an own-line
comment above a body, and an `if`'s trailing comment before `)`. Kept:
after `=`, `then`, `else`, `[`, a call's or a header's `(`, `+`, `.`, a unary `-`, `fn`, a header's
`)`, `let y =`, the callee; own-line before `+`, `then`, `else`, `(`, `]`;
trailing before `)`. The goldens hit it once (`comments`: `fn odd(x) = --
why`), and the disturber skips that declaration
(`Fmt/Tests/Disturbance.sw`).

The cause is in the tree, not the engine [source: `Syntax/Tree.sw`,
`Syntax/Parser.sw:362`]. The tree has comment slots only on list items,
arguments, bare statements and the note lines between statements and
declarations. The lexer attaches every comment to a token, but a comment on
any other token (`=`, `then`, an operator) has no slot, so the parser
counts the declaration's comments against its tokens' and makes it
`AsWritten` when one is missing.

## 2. The principle

**Ownership is lexical.** Every comment belongs to exactly one token, read
off the source by position alone, as both lexers already do: an own-line
comment to the token after it, a trailing comment to the token before it on
its line, a comment after the last token to the end of the file. Stitchwort
keeps its two existing adjustments (`comment_anchors`): a trailing comment
skips back over commas and closing brackets, which move freely around a
line's end (S39, D1012), and a comment on a comma that starts its line goes
to the next token. Sprig keeps its own: an item's comma is a token like any
other.

**Printing.** The printer prints each token's comments around it, in every
layout:

1. **Own-line comments of a token** go each on a line of their own,
   directly above it, at the column it starts at. If the layout didn't
   start a line at that token, the printer starts one: a *comment break*.
2. **A trailing comment of a token** goes right after it, one space
   between, and ends the line: nothing may follow it there (except, in
   Stitchwort, closing brackets and commas, as today). If the layout would
   put more code on that line, the printer breaks the line before that
   code: a comment break.
3. **A comment break is indented like a continuation line** of the
   construct it falls in: 2 more than the line that construct starts on
   (4 in a declaration header), as E2 already says for every break. The
   engine enforces a floor: never less than 2 more than the line being
   broken. So the code after a comment break is always deeper than the line
   it continues, which in both languages means it continues it and never
   starts a new statement.
4. **Groups and choices** as today: a group holding a comment breaks (E3,
   S38, S39), and a choice of layouts skips an option that would put code
   after a trailing comment (Rust's `fits` already does, Sprig's engine
   already breaks any `Line` after a waiting comment).

**The one special case.** Own-line comments before a closing bracket are
indented like the bracket's items (2 more than the closer), and the closer
goes on a line of its own (in Sprig, where closers otherwise hug, at the
column of the line its opener is on; in Stitchwort it is there already,
D1012). The general rule would put the comment at the closer's column,
outside the items it is about.

**What is not special-cased, and the layout it costs.** The general rule
gives a few layouts the house style otherwise never makes. Each happens
only where the author put a comment in that spot, and none occurs in the
repo today [measured, §1.1]:

- *A trailing comment after an operator.* Lines break before operators
  (S27, P6), so the operator stands alone on its line with its comment, and
  its right operand goes below at the same column. Keeping the author's
  `a + -- c` would need the chain to break after that one operator.
- *A trailing comment after a header's last parameter.* The conclusion's
  `:` starts the next header line.
- *A trailing comment after `fn`, a name, `.` or a unary `-`.* The rest of
  the construct continues on the next line.
- *A comment break where the layout would have stayed on one line*: the
  construct breaks there and only there; the rest of the line's layout is
  unchanged. A body after `:=` or `=` simply goes below, as when it doesn't
  fit.

A comment at the end of a block still moves to the next token, as today: an
own-line comment after a block's last statement is printed above the next
statement or declaration, at its column.

## 3. Each position, before and after

Sprig at width 40, Stitchwort at 120. "Today" is measured; "proposed" is
worked by hand from §2.

**After `=` or `:=` (trailing).** Both formatters keep it today. Proposed:
the body goes below, which is the input already.

```
fn odd(x) = -- why                         def f (x: Nat): Nat := -- why
  x % 2                                      x + 1
```

**After `let y =` / `let y :=`.** Same: the body goes below.

```
fn f(x) =                                  def f (x: Nat): Nat :=
  let y = -- c                               let y := -- c
    x                                          x
  y                                          y
```

**After `then` and `else` (trailing).** Stitchwort formats it today; Sprig
keeps it. Proposed for Sprig, the same shape: each branch goes below at 2.

```
fn f(x) =
  if x then -- after then
    1
  else -- after else
    2
```

**Before `then` and `else` (own-line).** Both keep it today. Proposed:
`else` already has a line at the `if`'s column, so its comment goes above
it there; `then` has none, so it gets a comment break at 2 more than the
`if`'s line.

```
fn f(a, b, c) =                            def f (x: Nat): Nat :=
  if a                                       if x == 0
    -- before then                             -- before then
    then b                                     then 1
  -- before else                             -- before else
  else c                                     else x
```

**After `[` or `(`.** Stitchwort formats `[` today and keeps `(`; Sprig
keeps both. Proposed: the bracket breaks, items below at 2.

```
let xs = [ -- after [                      def f (x: Nat): Nat :=
  1, 2]                                      Nat.add
                                               ( -- after (
let y = f( -- after (                            x)
  1,                                           x
  2
)
```

**After an operator.** Both keep it today. Proposed (the cost in §2):

```
let y = a                                  def f (x: Nat): Nat :=
  + -- after +                               x
  b                                            + -- after +
                                               x
```

Before an operator (own-line), Stitchwort formats today, and Sprig gets the
same shape:

```
let y = a
  -- before +
  + b
```

**After `|>`**, Stitchwort, kept today. Proposed, as for an operator:

```
def f (x: Nat): Nat :=
  x
    |> -- after |>
    Nat.succ
```

**Between a function and its argument.** A trailing comment after the
function: Stitchwort formats it today (the arguments go below); Sprig keeps
it. An own-line comment before the argument: both keep it today. Proposed:

```
let y = f -- after the callee              def f (x: Nat): Nat :=
  (1)                                        Nat.add
                                               -- before the argument
let y = f                                      x
  -- before (                                  x
  (1)
```

**Inside a header.** Stitchwort formats a comment after the name, after the
`:` and between parameters today, and keeps one after the last parameter's
`)` (the next code is the conclusion's `:`); Sprig keeps all of them.
Proposed:

```
fn f( -- inside a header                   def f
    x                                          (x: Nat) -- after a parameter
) = x                                          : Nat :=
                                             x
fn f(x) -- after the header
    = x                                    def f (x: Nat): Nat
                                               -- before :=
                                               := x
```

**Before a closing bracket (own-line), the special case.** Both keep it
today. Proposed:

```
let xs = [1, 2                             def f (x: Nat): List Nat := [
  -- before ]                                x,
]                                            x
                                             -- before ]
                                           ]
```

A trailing comment before a closer: Stitchwort formats it today (the closer
moves before the comment: `(x) -- c`, S39). Sprig gives the comment to the
token before it and puts the closer on the next line, as it already does
for an `if` ending in a comment (`closeAfter`):

```
let y = (a -- before )
)
```

**After an arm's `=>` or `with`.** Stitchwort keeps an `=>` comment today.
Proposed: the arm's body goes below.

```
def f (x: Nat): Nat := match x with -- after with
  | 0 => 1
  | Succ n => -- after =>
    n
```

**Sprig only: after `.`, a unary `-` or `fn`.** All kept today. Proposed:

```
let y = order. -- after .                  fn -- after fn
  items                                        f(x) = x
let y = - -- after minus
  x
```

## 4. Why the output is stable

**Idempotence.** The printer's choices depend only on the tree: its
constructs, token texts, each token's comments and the kept blank lines,
never the input's layout (D3558, D3560a). A comment break is chosen by the
printer from the tree, so formatting the output again reads the same tree
(the read-back property below) and makes the same choices: the same text.
If author-kept breaks are ever adopted (fmt-author-breaks.md, D3605), a
comment break must not count as one, or the second run would see a break
the first didn't have.

**The ownership invariant** the parser must keep, for the read-back proof:

> Every comment the lexer attaches to a token is held in the tree in that
> token's slot, and nowhere else. The parser carries comments; it never
> decides about them.

With that, read-back needs only that the printer puts each comment back on
the same token in the same role, which §2 guarantees by construction:

- an own-line comment is printed on a line of its own (rule 1 starts one
  if needed) directly before its token, so the lexer reads it as that
  token's;
- a trailing comment is printed directly after its token, and no code
  follows it on the line (rule 2), so the lexer reads it as that token's
  and no other code is swallowed by it;
- the code after a comment break is deeper than the line it continues
  (rule 3), so the parser reads the same construct. In Sprig a token on a
  deeper line after `=` starts a block, and a one-statement block is the
  same tree as a body on the `=` line (`Tree.sw`); in Stitchwort a deeper
  line after `:=` is the body, as before.

Comments are not part of either language's layout rule: an own-line comment
at any column inside a block doesn't end it (checked: a column-0 comment
between two statements of a Stitchwort block formats to the same tree
[measured]). So the column a comment line is printed at never matters to
the parse, only the next token's.

**In the toy's proof.** The tree gets a comment slot on every token, so the
comment count, `commentsAmong` and `AsWritten` go: `declaration` returns
what it parsed, always. Then:

- *Parser layer (D):* each rule that reads a token copies its comments into
  the tree. The comments ride along with the token texts the proofs already
  track; nothing is proved about where comments can't go.
- *Rules to tokens (E, `Spelled`):* every token's document is the same
  helper, comments above, text, comment after. The proof that the lexer
  reads each comment back onto its token is one lemma about that helper and
  one about the engine, instead of today's per-rule `CommentsApart`
  conditions and `suffixScan` over every rule (`Fmt/CommentProofs.sw`): the
  engine now guarantees, for any document, that no text follows a waiting
  comment on its line.
- *Columns (C):* the comment break's floor (rule 3) is one engine lemma:
  every line it starts is deeper than the one before.
- *Glue:* `formatDirect` has no `AsWritten` case, so it never re-parses,
  for every file. The cheap end state NOTES.md proposed ("re-parse only
  files with an `AsWritten` declaration") is no longer needed, and the
  decision it raised goes away.

**In `stitchwort fmt`.** The per-declaration checks stay, as the safety net
for a bug in any rule (a rule bug still costs an unformatted declaration,
never a wrong program). But S40's two reasons, "comment no rule places" and
"comment before a text block", can no longer happen and are removed; a
declaration kept for "comments" becomes a bug report, not a known gap. The
repo-wide count test stays at 0.

## 5. Consequences

**Toy (`tools/toyfmt`).**

- `Tree.sw`: a `Trivia` (own-line comments above, with the blank lines kept
  between them, and the trailing comment) on every token: on names,
  numbers and strings, and on each keyword and punctuation mark (`fn`,
  `let`, `=`, `(`, `)`, `,`, `[`, `]`, `if`, `then`, `else`, operators, `.`,
  `-`). `Item.comments`, `Item.trailing`, `Bare`'s trailing and the two
  `Note` constructors fold into the trivia of the first and last tokens.
  `AsWritten` goes. The tree's doc comment shrinks to the ownership rule.
- `Parser.sw`: `sign`, `name` and the leaf rules return the token's trivia
  with it; the comment count and `asWritten` go. `Comments.sw` goes.
- `Doc`: the engine's waiting-comment rule becomes a guarantee: text after
  a waiting comment breaks the line first, at the comment
  break's indentation. A `LineStart` like Rust's for own-line comments.
- `Rules.sw`: one `token` helper; `closeAfter` becomes the general rule for
  a closer after a trailing comment; every construct's parts after its
  first token sit in a `Nest` (free when nothing breaks).
- Tests: the 20 probes as a golden of awkward comments, the disturber over
  every declaration (no skip list), the `AsWritten` count test removed.
- Proofs: CommentProofs is rewritten smaller; ItemProofs and
  ExpressionProofs follow the tree's new fields; the other layers as above.
- Docs: P8 in toy-formatter.md; NOTES.md's AsWritten paragraph.

**`stitchwort fmt` (`crates/fmt`).**

- `engine.rs`: a `LineSuffix` leaves a break owed: the next text other than
  a closer or comma starts a new line first (today it is written on the
  same line and the comment drifts). `LineStart` breaks without counting.
  Both breaks use the comment-break indentation (the `Nest` in force, at
  least the broken line's indentation plus 2). Text blocks (S33) take the
  owed break before their `"""`, so "stranded" goes.
- `rules.rs`: own-line comments before a closer at the items' indentation;
  check that one-line options keep their continuation parts in a `Nest` so
  comment breaks land at the house indentation, not just the floor.
- `printer/mod.rs`: the two S40 reasons go.
- Tests: the 24 probes as printer tests (each formats, passes the three
  checks and is idempotent), with the outputs of §3.
- Docs: formatter-style.md S38–S40 (S40 becomes the comment-break rule),
  formatter-architecture.md's "a comment no rule places" line.

**The self-hosted formatter** (self-hosted-fmt.md) inherits the same rule
and no fallback for comments.

## 6. Plan

Toy first, as the brief asks, but the two lanes touch different code and
can run side by side. Past actuals for formatter lanes: the toy's stages A
to D took 19, 25, 30 and 30 min against estimates of 210, 270, 150 and 210;
stage 4 of the real formatter 15 min against 120; the median across lanes
has been about 0.3 of the estimate.

| Lane | Work | Model | Estimate | Expected actual |
|---|---|---|---|---|
| T | Toy: trivia on every token, parser carries them, engine's owed break and `LineStart`, the `token` helper and nests, `AsWritten` and `Comments.sw` removed, probes as a golden, disturber over everything, existing proofs repaired to the new tree, P8 and NOTES.md | Opus (the tree change runs through every proof file) | 3 h | ~1 h |
| R | `stitchwort fmt`: engine's owed break and comment-break indentation, closer special case, S40 reasons removed, the 24 probes as tests, formatter-style.md S38–S40 | Opus (the engine and a rule change of the style) | 2 h | ~40 min |

**Sequencing.** SW-3418 part 3 (the toy's direct proof) is running now and
works on the parser and rules proofs that lane T changes. Lane T should
start after it merges, and SW-3418's next part (layer E, `Spelled`) should
be written against the new tree, where it is smaller. Lane R can start at
once. Neither lane needs a broad test run: R's tests are the probes plus
the printer's own tests by name; the repo's output is unchanged, which the
verifier's fmt checks and Overmind's rolling check confirm.

## D3619: the principle and its layout cost

**The problem.** A comment in a spot no rule expects makes both formatters
give up on its whole declaration; the formatter is a partial function, and
in the toy it is the one case the correctness proof can't cover.

**The change.** Every comment stays next to the token it was written next
to; where that needs a line break, the formatter adds one, indented like
any continuation line. The cost is a few unusual layouts, only where an
author puts a comment in such a spot (none in the repo today): an operator
alone on its line with its comment, a header line starting with the
conclusion's `:`, a construct continuing on the next line after a comment
on `fn`, a name, `.` or `-`. The alternatives cost more: moving a comment
to a nearby token changes what it is next to (and needs a rule per
position), and special layouts per position (say, keeping `a + -- c` with
the operator at the line's end) add rules for cases that occur rarely.

**What it should do.** No declaration is ever left as written because of a
comment, in either formatter (0 of 44 probe positions instead of 28
[proposed]); the toy's `format` never re-parses; the repo's formatted
output is unchanged [measured: 0 declarations affected].

**D3619: adopt "a comment stays next to its token, and the formatter
breaks the line wherever that needs", accepting those rare layouts, for
both formatters? [rec: yes]**
