# The toy formatter: notes

`toyfmt` formats Sprig, a small language made up to rehearse the parts of
the self-hosted Stitchwort formatter (docs/proposals/toy-formatter.md).
This file keeps the friction met while writing it, and the timings, stage
by stage. Compiler built from `main` at e2b1cb075, 15 November 2026.

## What is here

| Namespace | Files | What |
|---|---|---|
| `Toy.Doc` | `Doc/Doc.sw`, `Doc/Print.sw` | The layout engine, a port of the core of `crates/fmt/src/printer/engine.rs` |
| `Toy.Doc.Tests` | `Doc/Tests/Engine.sw` | Six of the Rust engine's eight tests (not `Verbatim`, `LineStart`) |
| `Toy.Syntax` | `Syntax/Tree.sw`, `Syntax/Dump.sw` | Sprig's tree, which the parser makes and the rules read; a dump for tests |
| `Toy.Syntax` | `Syntax/Token.sw`, `Syntax/Lex.sw` | Tokens with their layout and comments; the keyword and operator tables; the lexer |
| `Toy.Syntax` | `Syntax/Parser.sw`, `Syntax/Comments.sw` | The parser over tokens, blocks by indentation; `parse` |
| `Toy.Syntax.Tests` | `Syntax/Tests/*.sw` | The lexer, the tables, the exact messages |
| `Toy.Fmt` | `Fmt/Rules.sw`, `Fmt/Format.sw` | The printing rules P1 to P10; `format`, parse then print |
| `Toy.Fmt.Tests` | `Fmt/Tests/*.sw` | Twelve goldens, the disturber and its tests; the goldens through the parser |
| `Toy.Timing` | `Timing/Timing.sw` | A generated file printed, then lexed, parsed or formatted, for timings |

Stage C adds the `{Files}` driver and `main`, calling `Toy.Fmt.format
source width`, which gives the `Printed` text or the parse error as
"line 3, column 9: expected ',' or ')', got 'b'".

## Stage B (SW-3341): the engine, the rules, the goldens, the disturber

### Timings

Printing a generated file (`Toy.Timing.main`: tree built, laid out, printed,
counted), Speedwell, load about 5, one run each [measured]:

| Output | `stitchwort run` | native (`build --native`) | Peak memory, native |
|---|---|---|---|
| 104 KB | 0.53 s (0.18 s after the 0.35 s start) | 0.22 s | 34 MB |
| 1.08 MB | 2.12 s (1.77 s after the start) | 0.36 s | 319 MB |

So the printer is linear, about 1.7 s/MB on the machine and 0.3 s/MB
native: printing is not where the real formatter's 20 seconds go. The
whole-format timing (lex, parse, print) waits for stage A's parser.

### Friction

1. **The tree has no `==`.** A syntax tree's types always refer to each
   other (an expression holds blocks, which hold statements, which hold
   expressions), and `==` isn't derived for types defined together:
   `E-INSTANCE-NONE ... its field declarations has type List (Spaced
   Declaration), which has no DecEq instance`. Stage A's test `parse source
   == tree` and stage D's validation (`format` checks that the output parses
   to the same erased tree) both need it. `Syntax/Dump.sw` writes the tree
   as text, and tests compare dumps; a proof needs a real decision, so the
   real formatter, with 94 node kinds, will want derived `DecEq` for
   mutually recursive types (or a hand-written one per kind).
2. **Recursion through a list in the tree needs a helper per list.**
   `arguments.map (item => item.value.layout)` inside the rules' mutual
   group is refused (`E-TERMINATION`, first for passing `Declaration.layout`
   unapplied, then for the call through `map`). The documented way round is
   a helper for each container, defined with the functions and taking the
   list apart by patterns (`itemDocs`, `statementLines`, `dumpItems`). A
   helper that returns parts (`Body.single: Body → Option (Expr, …)`) doesn't
   work either: what it returns isn't known to be smaller, so four rules
   match the body's shape inline instead. The real formatter's 94 kinds will
   repeat this everywhere; recursion through `List.map` on a field of the
   scrutinee (nested fixpoints, as Coq has) would remove it.
3. **A constructor can't share its name with a type its fields use.** The
   Rust engine's `Doc::Text(String, usize)` ported as `| Text (text: Text)`
   is an error: "a data type's fields can mention the type itself, but not
   its constructors". Renamed `Chunk`.
4. **Constructors of different types collide even where the type is
   known** (toy-formatter.md §6 item 3, SW-510): a `Line` in `Doc` and one in
   a token type make `| Line =>` in a `match` on a `Doc` `E-AMBIGUOUS`. So
   names were chosen to stay apart: `Doc.Flatten` (Rust's `Flat`) beside the
   printer's `Mode.Flat`; the tree's `Var`, `NumberLiteral`, `StringLiteral`
   so that stage A's token kinds can be `Name`, `Number`, `Str`; the
   disturber's `WordPiece`, `SymbolRun`.
5. **No `List.intersperse`.** `Text.joinWith` exists, but nothing puts a
   separator between the items of a general list: written twice
   (`Doc.joinLines`, `Doc.joinedWith`).
6. **A tuple accumulator needs its type written.** `text.lines.foldLeft
   ([], None, 0) (...)` is `E-UNSOLVED` at `[]` until annotated `(([], None,
   0): (List Chunk, Option Chunk, Nat))`, though the step function's use says
   it.
7. **The formatter moves a record literal holding text blocks below `:=`**
   and re-indents all of it (`def groups: Golden :=` then `{` on the next
   line), where the same literal without text blocks opens on the `:=` line
   (games/rogue's `quiet`). The goldens all have that shape.
8. **No clock.** `IO` can't tell the time, so the toy's per-phase timings
   (lex, parse, print) can only be taken from outside, one `main` per phase.
9. **Small:** `W-RECEIVER-NOT-FIRST` moved Rust's `Doc::nest(indent, doc)`
   and a `joinWith (docs) (separator)` out of `Doc`'s namespace, since their
   first parameter isn't a `Doc`.

What went well: the engine, ported almost line for line, passed all its
tests on the first run, and a failing golden's report (the two texts line by
line, with the first difference's line and column) found both wrong
expectations at once.

### What the disturber does

A sample, from the comments golden with seed 5:

```text
-- Totals for one order.
fn   total(order)= 
    -- the base price
    let base= sum( order.items) -- before tax
    base+  tax(base)
let weights  =  [


      -- light
      1 ,
        2 , -- two
      3]
fn odd(x) = -- why
  x  %  2
```

The last declaration is left alone: its comment is where no rule places
one, so formatting keeps it as written.

## Stage A (SW-3340): the lexer and the parser

### How it works

- **Lexer** (`Syntax/Lex.sw`): `Parse` over characters, one lexeme at a
  time chosen by a `match` on the next characters (no `oneOf`), each in
  `Parse.located`. Every character is in a lexeme, spaces and line breaks
  too, so the lexemes' slices joined are the source (tested on arrows, a
  combining accent, U+10FFFF and a tab). Texts are cut with `Text.slice`.
  Only an unclosed string or a bad escape fails to lex; any other
  character becomes a `Stray` token, which the parser reports where it
  stands (`got '$'`). Tabs and `\r` are stray, so CRLF files don't parse.
- **Tables** by text patterns: `Keyword.fromWord`, `symbols` (operators
  and `=`), with `punctuation` by character. `nameIsNoKeyword` (a word that
  lexes as a name spells no keyword) is proved by `cases` alone.
- **Tokens** carry their layout and comments: `startsLine`, `column`,
  the own-line comments and blank lines `above` them, the `trailing`
  comment after them, and on the last token those `below` it.
- **Parser** (`Syntax/Parser.sw`): `Parse.tokens`. Every token is read
  through a `Layout`: in brackets anything goes; in a statement, a token
  that starts a line must be deeper than the statement's column (`else`
  may stand at it). A body whose next token starts a deeper line is a
  block at that token's column. So a statement ends where the next line
  isn't deeper, with no indent or dedent tokens.
- **Comments**: own-line ones are taken from the first token of a
  declaration, statement, item or argument; trailing ones from the last
  token of an item (its comma, if it has one) or a bare statement. A bare
  statement or item ending in an `if` leaves it to the `if`'s branch. Then
  the declaration's comments are counted (`Syntax/Comments.sw`) against
  those among its tokens: if any is missing, the declaration is
  `AsWritten`, cut from its first token to the end of its last token or of
  the comment after it. This validation is all of P8's "anywhere else"
  rule: no case analysis of where comments can't go.

All twelve goldens parse to their trees, both texts format to the
formatted one, and all 50 disturbances of each format back, on the first
run.

### Timings

Generated file (`Toy.Timing.main -- PHASE COPIES`), Speedwell, load 8–12,
one run each [measured]. Each phase's figure is its run's time less the
`print` run's (making the input); "parse" includes lexing and "format"
includes both.

| | 100 KB, `run` | 1.04 MB, `run` | 100 KB, native | 1.04 MB, native |
|---|---|---|---|---|
| Making the input (`print`) | 0.61 s | 2.20 s | 0.03 s* | 0.37 s |
| Lexing (209,000 tokens per MB) | +0.29 s | +3.07 s | +0.13 s | +1.33 s |
| Lexing and parsing | +0.78 s | +7.83 s | +0.38 s | +3.73 s |
| Whole format | +0.94 s | +9.67 s | +0.41 s | +4.23 s |
| Peak memory, format | 199 MB | 509 MB | 46 MB | 380 MB |

\* User time: that run was the first and took 0.26 s real. The 100 KB
native column is by user time throughout; the figures are a tenth of the
1 MB ones, so every phase is linear.

So the whole format is **4.2 s/MB native** (lexing 1.3, parsing 2.4,
printing 0.5), the low end of the plan's 4–8 s estimate, and 9.7 s/MB on
the machine. Parsing costs more than lexing: each operand goes through six
`chainLeft` levels, each trying an operator (a failed `optional` and a
note) after it, and calls and fields a `oneOf`. Precedence climbing would
try one operator token per operand; not profiled, and not stage A's job.
At this rate the real formatter's 6.5 MB would take about 27 s native with
combinators, against the plan's 20 s.

### Friction

1. **`Parse.recursive` takes no argument** (about 5 min). The parser
   passes the layout down, so the nested parser is `Layout → {Parse …}
   Expr`, which `recursive`'s `() → {Parse t} a` can't be. Wrote `nested`,
   the same thing with an argument (eight lines). A std
   `Parse.recursiveWith` would do; the real twin, which passes modes
   down (self-hosted-fmt.md §2), needs the same.
2. **Mutually recursive parsers need fuel by hand** (about 5 min). A
   body holds a block, which holds statements, which hold bodies:
   `E-TERMINATION`, as the stage B rules met (friction 2 above). `bodyFuel`
   threads a depth bound. Every layout-sensitive parser will repeat this;
   `{Partial}` was the other way out.
3. **`Parse.tokens` takes only tokens** (about 10 min of design).
   Comments after the last token have nowhere to go but the last token (the
   `below` field, set on one token in all the file), and a file with no
   tokens loses its comments altogether, so `commentsOnly` re-reads the
   source. An end-of-input token would give a message of `got ''`, since
   `Parse.tokenFound` slices the source. A lexer that could return trailing
   trivia beside its tokens, or an end token that messages call "the end of
   the input", would remove both workarounds.
4. **The parser can't see the token it just read** (about 10 min). A
   trailing comment belongs to whatever ends at the token before it, so
   items need their last token; `lastSince` gets it back from a mark's
   `rest` and the offsets, walking the item again. A `Parse.previous()`, or
   a mark that held the item before it, would make it one step.
5. **A layout-rejected token reads as a wrong token.** When a line starts
   too far left, the parser's messages still list what it would have taken
   there (`expected an operator, got 'x'`), though nothing was possible
   at that position. Two messages of the parser's own cover the common
   cases: "this line's indentation matches no block it could belong to"
   and "'else' must not start a line to the left of its 'if' statement".
   `Parse.whole` notes "the end" after the parser returns, so the first of
   these has to be raised before the file parser returns, or it reads
   "…; expected the end of the input". Small.
6. **A dotted helper isn't imported by `(..)`** (2 min): `def
   Located.slice` in `Toy.Syntax` couldn't be called as `Located.slice`
   from the tests' namespace with `import Toy.Syntax (..)` (`E-UNKNOWN-NAME`).
   Renamed it `cut`.
7. **Small:** `Parse` isn't in the prelude, so `{Parse Char}` needs `import
   Std (Parse)` (the note says so); a quiet failure is `Empty.absurd
   Parse.stop()`, which needs `import Std (Empty)`; a function `keyword`
   and the table `keyword` in two files of the namespace are `E-DUPLICATE`.

What went well: the layout rule as a parameter of the token reader is about
ten lines and read naturally; validation by counting comments made P8's
fallback free; `cases` proved the keyword theorem unaided; and once it
checked, everything passed on the first run, the 600 disturbed texts
included.
