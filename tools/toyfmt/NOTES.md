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
| `Toy.Fmt` | `Fmt/Driver.sw`, `Fmt/Cli.sw` | The `{Files}` loop (walk, format, write only what changes) and the command line, `Toy.Fmt.main` |
| `Toy.Fmt.Tests` | `Fmt/Tests/Driver.sw` | The loop and the command line under `Files.simulate`, with a write-counting handler |
| `Toy.Syntax.Proofs`, `Toy.Fmt.Proofs` | `Syntax/Proofs.sw`, `Fmt/Proofs.sw` | Stage D's theorems: `lexCovers`, `formatRoundTrip`, `formatIdempotent`, and the file loop's under `Files.simulate` |
| `Toy.Doc.Proofs`, `Toy.Fmt.Proofs` | `Doc/Words.sw`, `Doc/Columns.sw`, `Fmt/WordProofs.sw` | SW-3418 part 5: every reading writes the document's words in order; the rules' document has the file's tokens and comments; the printer's column is the text's |
| `Toy.Fmt.Proofs` | `Fmt/TextProofs.sw`, `Fmt/JoinProofs.sw`, `Fmt/RuleJoinProofs.sw` | SW-3418 part 7: the lexer's texts as predicates; every rule joins; a file with the lexer's texts, printed at any width, lexes to its pieces (`printedLexes`) |
| `Toy.Fmt.Proofs` | `Fmt/LexTextProofs.sw`, `Fmt/StringProofs.sw`, `Fmt/ParsedProofs.sw` | SW-3418 parts 8 and 9: the lexer's tokens have the lexer's texts; the parser copies them into the tree (`parseLexical`); a parsed file, printed at any width, lexes to its pieces (`parsedPrintLexes`) |
| `Toy.Doc.Proofs`, `Toy.Fmt.Proofs`, `Toy.Fmt.Tests` | `Doc/Places.sw`, `Fmt/PlaceProofs.sw`, `Fmt/Tests/Places.sw` | SW-3418 part 10: the printed tokens from the pieces alone, each with its line start and column (`placed`, `parsedPrintTokens`); every word of a print is where its document lays it (`Lays`, `printLays`); a runnable probe of `Lays` over the goldens |
| `Toy.Fmt.Proofs` | `Fmt/LaidProofs.sw` | SW-3418 part 11: a token and a closing bracket with their comments lay exactly their events (`tokenLays`, `closerRule`); zones and rule triples for the rules' half of positions (`Zone`, `Rule`, `tokenRule`) |
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
   **Fixed (SW-3371):** types defined together, and types nested in the
   program's own `Spaced`, now get derived `==`, `<` and `${…}`, so `Expr`,
   `Item`, `Statement`, `Body`, `Declaration` and `SourceFile` have them;
   the golden parsing test compares trees with `==`. The layout tests still
   compare dumps against expected text, which reads well as it is.
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

## Stage C (SW-3342): the file loop, the command line, the executable

### How it works

- `Toy.Fmt.formatPaths options paths: {Files} List Outcome`. Each path is
  `Files.info`-ed: a file is formatted whatever its extension, a folder is
  walked a level at a time (`walkLevels`, at most 32 deep; `Files.walk`
  isn't in std, so this is F3's starting point) for `.sprig` files. An
  unreadable folder, a missing path and a file that doesn't parse are
  `Problem` values with the path in the sentence (`src/bad.sprig:1:8:
  expected an expression, ...`, made from the parser's "line 1, column 8:"
  by `locate`); the others are still done. A file is written only when its
  formatted text differs, and not at all with `--check`.
- `toyfmt [--check] [--width N] PATH...` (`Toy.Fmt.run arguments:
  {Files, IO} ExitStatus`; `main` is `run IO.args()`). Changed paths go to
  standard output (`IO.print`), problems and "N declarations left as
  written" to standard error (`IO.printError`). It exits 0, 1 (`--check` found
  a file to change) or 2 (a bad command line, or a path it couldn't read or parse). Run
  it with `stitchwort run Toy.Fmt.main -- ARGS` in the project, or
  `stitchwort build --native Toy.Fmt.main -o toyfmt` (the target is
  named, because `Toy.Timing.main` is a second `main` in the project).
- Tests (`Fmt/Tests/Driver.sw`, 13): under `Files.simulate`, with
  `countingWrites`, a handler over `Files` that lets every operation
  through and counts the writes: a formatted file and a second run write
  nothing, `--check` writes nothing, a missing path or a file in the way
  is a value and the rest are done, a broken file leaves the disk as it
  was. `run` itself is tested under `IO.simulate` inside `Files.simulate`.
  The end-to-end test is `toyfmt_formats_a_folder_under_run_and_built` in
  `crates/cli/tests/running/build.rs` (it needs that file's helpers, the
  runtime library and a C compiler): a temporary folder with a file to
  rewrite, a formatted one, a broken one, a nested folder and a `.txt`,
  run under `stitchwort run`, the plain built executable and the native
  one; it compares the folder after each run, the formatted file's
  modification time, the exit codes, and the usage line for a bad flag.

### Timings

100 files in 10 folders, 771 KB in all (95 declarations a file, long `fn`
and `let` lines), `toyfmt DIR`, one run each, Speedwell at load 27 to 50 from
other lanes, so rough [measured]:

| | native | `stitchwort run` |
|---|---|---|
| Every file rewritten | 3.6 s (4.7 s/MB) | 8.4 s (10.9 s/MB) |
| Second run, nothing to write | 3.5 s (4.5 s/MB) | not run |
| `--check` | 4.0 s (5.2 s/MB), at load 49 | not run |
| Peak memory, native | 10 MB (files are done one at a time) | |

So the loop adds nothing measurable to stage A's 4.2 s/MB whole format
(reading, walking 110 folders and entries, and writing 100 files are
noise): the cost is the lexer and parser, and the executable's start is
well under 0.1 s. Writing costs about 0.1 s for all 100 files. The 1 MB
figure is about 4.6 s native; the real formatter's 6.5 MB would be about
30 s by this.

### Friction

1. **No exit status but 0 and 1** (SW-3345; resolved by SW-3403: `main` returns an `ExitStatus`, the toy exits 0, 1 for `--check` finding a change, 2 for a problem or a bad command line, as `stitchwort fmt` does). Was: a formatter wants 0 = clean,
   1 = would change, 2 = could not parse or read; the loop knows which, but
   `Fail` is all there is, so both read 1, and `--check`'s message is the
   only way to tell them apart.
2. **A handler over `Files` is state-passing by hand.** `countingWrites`
   is the same eleven lines as `Files.simulate` with the disk replaced by a
   count, and it has to name each of the four operations to pass it on. A
   std `Files.tracing` or a general "handle every operation by forwarding"
   would make a counting or logging wrapper one line (and let a test count
   reads too).
3. **`Files.simulate` can't see a modification time.** The end-to-end test
   uses the real file's mtime to show a file wasn't written; under
   simulation the write counter is the only evidence. A `Disk` that
   recorded its writes (`writes: List Path`) would make "left alone" a plain
   equality on the result.
4. **A test file can't import its own project from outside it.**
   `stitchwort test src/Toy/Fmt/Tests/Driver.sw` says there's no namespace
   `Toy.Fmt`; a file target runs outside the project, so tests are run by
   namespace or `--only NAME`. (`--only` with a name as long as a sentence is
   the way to run one test.)
5. **A project with two `main`s can't be built by its folder:** `build`
   wants the one namespace with a `main`, and the toy has the timing one
   too. Naming the function (`Toy.Fmt.main`) works.
6. **Small:** no `Text.after`/`splitOnce`, so `locate` splits at ", column "
   and then at ": " and joins the rest back.

### What stage D (the proofs) needs from here

`formatFile` is the one place text goes from disk to disk, so a theorem about
it is the loop's: that the file is written only if its text differs (the
write-counting test, as a lemma over `Files.simulate`'s laws, which are
`rfl`), and that what is written is `format`'s output. The proofs the plan's
§3 names are about `format` itself (round trip, idempotence), and need the
erased tree and derived `==` for the tree (stage B friction 1, which
SW-3371 fixed: `parse source == Ok tree` works now).

## Speed (SW-3383): profiled, and the toy's handlers taken out of the hot paths

Profiled natively with samply and the `call-counts` runtime on
`Toy.Timing.main -- PHASE 2600` (933 KB), Speedwell. Times are user
seconds, median of 3 at load about 3.5; instructions (median of 5) are
the steadier figure [measured]:

| Phase | Before | After |
|---|---|---|
| Lexing | 1.15 s, 16.4 G instructions | 0.68 s, 9.3 G |
| Parsing (beyond lexing) | 2.08 s, 29.0 G | 0.91 s, 12.2 G |
| Printing | 0.29 s, 4.4 G | 0.32 s, 4.4 G |
| Whole format | 3.52 s (3.8 s/MB), 49.8 G | 1.91 s (2.05 s/MB), 25.9 G |

`stitchwort run`, one run each at load 25: whole format 9.4 s to 5.2 s.

**Where the time was.** Not in any one function: three quarters of it was
the effect runtime and the allocator, per `Parse` operation. Counted: a
format did 5.4 M operations, each crossing 1.6 forwarding handlers on
average (8.7 M crossings), and allocated about 60 M objects. A micro-probe
puts one operation (`Parse.mark`) at about 4,300 instructions natively and
a `Parse.optional` round at about 6,300 more. So the cost is the number of
operations and handlers, and the toy's grammar made far more than it
needed:

- every operand went through six `Parse.chainLeft` levels, each trying its
  operator under its own handler (`many`, then `optional`), plus a `many`
  for negations and a `many` of a two-way `oneOf` for calls and fields:
  nine handlers and about thirty operations per operand;
- every lexeme was a `Parse.many` round (a handler) over `Parse.located`
  (two marks) over a third mark to look at the next characters;
- every list item's comma and every list's closer was a `Parse.optional`.

**The changes** (all in the toy; messages unchanged, checked by running
the old and new executables on 9,000 mutated goldens, bad strings and
stray characters among them, with identical output):

1. Operators by precedence climbing (`chain`, `chainFrom`), negations and
   calls and fields by one look at the next token. A handler is installed
   only where an operator, `(` or `.` was found, so that one without its
   operand is still left unread. Wherever the old grammar noted "an
   operator", "'('", "'.'" or "an expression" as expected, the new one
   notes the same. Parsing: 2.08 s to 0.95 s.
2. Lexemes in a loop of their own (`lexemesFrom`): a lexeme fails only on
   a bad string, which fails the whole lex, so it needs no handler, and the
   mark after one lexeme is the start of the next. Lexing: 1.20 s to
   0.72 s.
3. A comma or closing bracket by a look at the next token
   (`signInBrackets`). Parsing: 0.99 s to 0.91 s.

**Tried and dropped:** the runtime's freeing queue on the stack
(`SmallVec`) instead of a heap `Vec` per freed cell with children (2.8% of
the profile was that `Vec` growing): instructions rose 1%, cycles the
same.

**What is left**, by instructions: lexing and parsing are still about half
`Parse` operations (2.4 M of them, at about 4,000 instructions each), and
about a tenth the list of characters (`toList`, and `span` building,
reversing and counting what it takes: about 1,200 instructions a character
in a probe). Neither is the toy's to fix: the first is the effect runtime's
cost per operation (operations in place, docs/proposals/operations-in-place.md,
paused at stage B, D3430, D3465), the second `Parse` reading a list
(D3597's slices). By this rate the real formatter's 6.5 MB would take about
13 s natively, against the plan's 20 s, if its grammar costs per byte what
Sprig's does; a bigger grammar will cost more.

## Std Parse from the toy (SW-3367, SW-3391)

What stage A's friction asked of std, now there, and the toy moved onto it:

| Friction | Std | In the toy |
|---|---|---|
| 1 `recursive` takes no argument | `Parse.recursiveWith body argument` | `nested`, `nestedFuel` removed |
| (speed) precedence climbing | `Parse.operators what levels operand`, levels with a `Parse.Associativity` | `chain`, `chainNested`, `chainFrom` removed; `operatorLevels layout` |
| (speed) a handler per lexeme | `Parse.locatedToEnd lexeme` (and `Parse.manyToEnd`, for any item) | `lexemes()` |
| 3 comments after the last token | `Parse.tokensWith input lexer parser`: the lexer returns `(tokens, extra)`, the parser takes `extra` | `lex` returns the tokens and the trailing trivia; `Token.below` and `commentsOnly` removed |
| 4 the last item read | `Parse.lastRead start finish` (a function of two marks) | `lastSince` |
| 6 `(..)` and a dotted helper | not a bug, see below | |

Native, `Toy.Timing.main -- PHASE 2600` (933 KB), user seconds, median of 3,
load 3 to 5 [measured]; the print phase (0.29 s) is inside each:

| Phase | Hand-written in the toy (SW-3383) | `Parse.operators` + `Parse.locatedToEnd` | `Parse.many` for lexemes |
|---|---|---|---|
| lex | 0.97 s | 0.97 s | 1.49 s |
| lex and parse | 1.84 s | 1.97 s | |
| format | 2.18 s | 2.30 s | |

`Parse.locatedToEnd` matches the toy's own loop and beats `many` by a third
of the lexing time. `Parse.operators` is 0.13 s (7%) slower than the toy's
own climbing: it scans the level table for each operator token (up to six
closure calls) and the toy builds the table per expression, since the
layout is in it. A std function that took one classifier,
`item → Option (level, associativity, combine)`, would skip the scan.

**Friction 6 was not a bug.** `import N (..)` brings the names declared
directly in `N`, and a type with its namespace (`Foo.bar` and `foo.bar`
work after `import A (..)`), but not a namespace that holds only helpers
(`def Helper.double` in `A` isn't reached as `Helper.double` after
`import A (..)`; `import A (Helper)` reaches it). `def Located.slice` made
such a namespace, `Located` not being a type of `Toy.Syntax` (`Parse.Located`
is the library's, which a program can't add to). docs/syntax.md says so;
the error says nothing about it. Constructors aren't brought by `(..)`
either (`Mk` of `A.Foo`: `A.Foo.Mk`).

**No `Parse.previous()`.** A mark that held the last item read would make
every read keep it: `Parse.State.advance` runs per operation, a `span` would
have to find its last item, and `Parse.Mark` is built and matched in dozens of places
(the handlers, `Parse/Reads.sw` and `Runs.sw`). `Parse.lastRead` does the
walk the toy did, once, in std.

## Stage D (SW-3343): the proofs

### What changed in the program

- `lex source` is now pure and checked: `Result Lexed Text`, where `Lexed`
  has the lexemes, the tokens made from them and the trivia after the last
  token. It runs `Parse.all source lexemes`, then answers only if `covers`
  (the lexemes' slices joined `==` the source). `parse` runs `lex`, then
  `Parse.whole` and `Parse.tokensMessage`, the three steps of
  `Parse.tokensWith`, taken apart so the check sits between the first two.
  Messages are unchanged (the tests, which compare them, pass).
- `format source width` is now a `FormatResult`: `Stable printed` or
  `Refused message`. It parses, prints the tree, parses the output and
  answers `Stable` only if `parse printed.text == Ok tree`. The rules are
  unchanged: the tree was already the erased tree (no layout in it), so
  "the printer reads only the tree" needed no new type.
- `Driver.sw` matches `Stable`/`Refused`; `Timing.sw` and the lexer tests
  use `lex`'s `Lexed`.

### The theorems

All proved, none with an extra hypothesis; `stitchwort audit` on both proof
namespaces: no failures (the warnings are the theorems whose hypotheses are
about a `Disk` and a successful `format`, which the audit's random inputs
never satisfy: the tests in `Fmt/Tests/Validation.sw` and `Driver.sw` run
the same shapes).

| Theorem | Says | How |
|---|---|---|
| `lexCovers` | `lex source = Ok lexed` gives `Text.concat (lexed.lexemes.map (cut source)) = source` | unfold `lex`, `match` on the run's result and on `covers`; `DecEq.sound` on the check; 6 lines |
| `formatChecked` (lemma) | `format source width = Stable output` gives a `tree` with `parse source = Ok tree`, `output = tree.print width`, `parse output.text = Ok tree` | `match` on `parse source` and on the check; constructor injectivity of `Stable` by `Eq.cong` with a projection |
| `formatRoundTrip` | the same without the middle part | from `formatChecked` |
| `formatIdempotent` | `format output.text width = Stable output` | from `formatChecked`: rewrite the reparse, the check on the same tree is true again |
| `formatFileUnchanged`, `formatFileWouldChange`, `formatFileRewrites`, `formatFileRefusedWrite`, `formatFileRefused` | what `formatFile` does under `Files.simulate`: no write when the text is the same, with `--check`, or on a parse error; one write of `format`'s text at its path otherwise | `rewrite` the read and the answer, one `match` on `printed.text == source`; each is a few lines |
| `readAfterWrite` | a write the disk allows reads back as the text written | five `match`es on the conditions of `Disk.write`, `Map.getInsert` |
| `formatFileSettles` | after the disk took `format`'s text, the next `formatFile` there is `Unchanged` and writes nothing | `readAfterWrite`, `formatIdempotent`, `formatFileUnchanged` |

Idempotence took minutes, not the day the plan allowed: with the check in
`format` and the tree as the rules' only input, the proof never meets a
printing rule or the engine. The stage's proof effort was about
15 minutes of lane time on the clock (13:08 to 13:22), including the file-loop
theorems and `readAfterWrite`.

Breaking the program makes the proofs fail, checked both ways: `if True`
for `format`'s check (`E-NONEXHAUSTIVE` in `formatChecked`), and for
`lex`'s (the same in `lexCovers`).

### Timings of the validation

Native `Toy.Timing.main -- PHASE 2600` (933 KB), user seconds, median of 3
(the three runs agreed within 0.02 s), Speedwell at load 50 [measured].
"Before" is the code at `main` (40708fe3d), "after" this branch, both built
by the same compiler; the print phase (0.30 s) is inside each.

| Phase | Before | After | Why |
|---|---|---|---|
| print | 0.30 s | 0.30 s | unchanged |
| lex | 1.02 s | 1.07 s | `covers`: joining 187,000 slices and comparing 933 KB, +5% |
| lex and parse | 2.08 s | 2.13 s | the same check |
| whole format | 2.39 s | 4.29 s | the output is lexed (checked) and parsed a second time and compared with the tree: +1.9 s, +80% |

So validation costs one more parse of the output: 2.0 s/MB native for the
format of an already formatted file (a file that changes costs the same,
the output's size). The plan expects this ("it doubles the run time" for
the by-validation idempotence of its first design); for the real
formatter's 6.5 MB at the toy's rate that is about +13 s, which the
validation could save by comparing the output's tokens first, or by
parsing the output only in a debug build, at the price of the theorems
then being about the checked build. The lexemes' coverage check alone is
about 5% of lexing (0.05 s per MB), cheap enough to keep always.

### Friction

1. **The tokens don't keep the spaces, so `lexCovers` is about the
   lexemes.** The plan said "the tokens' trivia and text slices, joined,
   are the source", but a `Token` carries blank lines as a flag and drops
   spaces and line breaks; the lexemes (every character in one) are the
   covering list, and the tokens are made from them. Not a loss for the
   formatter, which doesn't need the spaces; the real lexer's trivia keep
   them, so there the statement is about the tokens.
2. **An effectful lexer can't be reasoned about, so the check has to run
   outside it.** `Parse.tokensWith` runs the lexer, then the parser, inside
   one `{Fail}`; a check made between them would be inside the effect, and
   the theorem would have to reason about the handler. Taking the three
   steps apart (`Parse.all`, `Parse.whole`, `Parse.tokensMessage`: all
   public) put the check in plain code. A std
   `Parse.tokensWith` that took a check (`(extra, tokens) → Option Text`),
   or a `Parse.tokensResult` returning a `Result`, would save the
   copy.
3. **Constructor injectivity is a hand-written projection.**
   `Stable a = Stable b` to `a = b` is `Eq.cong (printedOr a) h`, with a
   projection function written for the purpose (`Result.okInjective` does it
   for `Ok`). Every user-defined constructor with fields needs one; derived
   `Foo.injective` lemmas would remove it (the plan's gap 1, `cases` not
   using the equation it derives, is the other way).
4. **`match` without the impossible arms works.** `lexCovers` and
   `readAfterWrite` leave out the arms `h` rules out (`W-UNREACHABLE` says
   to delete them), which is what keeps them short.
5. **`==` on trees and `Result`s is all the validation needs.** `parse text
   == Ok tree` is derived (SW-3371) and `DecEq.sound` / `DecEq.soundFalse`
   take it to `=` and `≠`; nothing was missing.
6. **For the real formatter:** its rewrites change the tree, so its
   `Stable` check compares the output's tree with the *rewritten* source
   tree, and `formatChecked` keeps the same shape with `rewrite tree` in
   place of `tree` on the left; the printing function must still take
   only the (rewritten) erased tree, so the idempotence proof also needs
   "rewriting the rewritten tree changes nothing" to be part of what the
   check tests, as the plan's theorem 2 says.


## Proving the printer directly (SW-3418)

The goal: `parse (print width tree) = Ok tree` for every tree the parser
produces and every width, so `format` can drop its re-parse. A 3-hour
experiment; the theorem is not complete, so `format` keeps its check and
there is no `formatDirect` yet.

### The plan

Five layers, each independent of the others' internals:

- **A. The engine.** `print` refines a width-free reading of `Doc` (each
  group flat or broken, each choice any option, each fill separator a
  space or a break), so width only chooses among readings and every later
  layer holds at every width for free. Needs: budgets that never run out
  (done), and that a waiting trailing comment is never followed by text on
  its line, which is where `fits` has to be exactly right.
- **B. Lexing.** The text of a reading lexes to the tree's tokens, with
  line starts and columns from the breaks. Needs std lemmas about `Text`
  and about the lexer's `locatedToEnd`, and the munch conditions between
  neighbouring chunks (no `-` before `-`: bug 1 below).
- **C. The layout rule.** Which breaks land at a statement's own column:
  only before `else`, `)` and `]`. A structural fact about the rules, with
  no width in it (done, rule side).
- **D. The parser reads it back**, by induction over the tree with std's
  `Parse.Runs` (atoms and suffix ends done). Every expression form above an
  atom goes through `Parse.operators`, which has no `Runs` lemma yet; that
  lemma (precedence climbing with backtracking, fuel and depth) is the
  gate for the rest of D.
- **WF.** What the parser guarantees about its trees (names aren't
  keywords, chains are shaped by precedence, a body's last line isn't a
  note, ...), as a predicate D assumes. Either proved of the parser (as
  long again as D) or checked at run time (a linear walk, far cheaper than
  a re-parse, but still a check).

### What is proved

- `LayoutProofs.sw` (layer C): every statement and laid-out declaration
  breaks at its own column only before `else`, `)` or `]`
  (`statementScan`, `declarationScan`).
- `CommentProofs.sw` (the rules' half of "comments keep their owners"):
  in every document the rules build for a tree whose comments stand where
  the parser puts them, every trailing comment is followed by a line break
  before any text or another comment, whichever way groups, choices and
  fills go; and a document ends with a comment waiting exactly when its
  tree does (`exprSuffix`, `statementSuffix`, `declarationSuffix`).
- `ParserProofs.sw` (layer D, first pieces): a name token reads back as
  `Var` (`runsAtomName`); suffixes stop at a token that isn't `(` or `.`
  (`runsSuffixesEnd`).
- `Doc/Proofs.sw` (layer A, budgets): `print`'s 3 * size + 3 is enough
  for the printer's steps and for every `fits` it asks, so a larger
  budget prints the same text (`printBudgetEnough`). This rules out `fits`
  answering "fits" because it ran out.

Each was checked to fail when the rule or budget it depends on is broken
(a block not one level deeper, `closeAfter` without its line break, a
fill's size counted once).

### Bugs the proof work found

The first two were caught at run time by the re-parse (`format` answered
`Refused`), so no output was ever wrong; with the check gone they would
have been.

1. `let y = - -x` printed `--x`, which reads as a comment. `Negate` now
   puts a space before an operand that starts with `-`.
2. A comma or closing bracket after an `if` whose last branch ends in a
   trailing comment went on the comment's line, inside the comment. It now
   goes on the next line (`closeAfter`).

3. In the engine: `fits` started every measurement with no comment
   waiting, so a group that began with a line straight after a trailing
   comment could stay flat and print code after the comment
   (`f a -- c` then a group `[Line, b]` printed `f a b -- c`). Groups,
   fill items and choices now measure with the waiting comment counted
   (`Printer.fitsHere`). The rules never build that shape (the comment
   proofs say what follows a comment is a break, and in the rules it is
   always a hard line, a fill separator or a line in the same group), so
   no output changes; the engine proof needs it.

### Estimate [estimated, low confidence]

From the calibration here (layer C's rule side about 20 min for 15
lemmas; each parser atom lemma about 10 min; the comment group about
40 min; the budgets about 15 min):

| Layer | Left | Estimate |
|---|---|---|
| A | the suffix simulation over `run` and `fits`; the refinement | 2-4 days |
| B | lexing, with std `Text` and `locatedToEnd` lemmas | 2-4 days |
| C | reading the layout back as the same body | 0.5-1 day |
| D | `Parse.operators` `Runs` lemma (3-6 h), then items, if/else, blocks, declarations | 4-8 days |
| WF | proved of the parser, or a run-time walk | 2-4 days, or 0.5 day |
| Glue | `formatDirect`, its round trip and idempotence | 0.5 day |

About 2-4 weeks of lane time for the toy. The expensive layers (A, B, D)
don't depend on the style rules; only C-like structural lemmas and the
comment group do, and those were the cheap ones, so changing the style
needn't break the expensive proofs.

For the real formatter (94 node kinds, rewrites, the left-as-written
fallback): D, WF and the rule-side lemmas grow with the number of node
kinds, about 5-6 times the toy's 17 forms (10 expressions, 3 statements,
4 declarations); A doesn't grow (one engine) and B grows with the token
kinds. That gives roughly 2-4 months of lane time [estimated, very low
confidence: no piece of the real formatter was tried]. Rewrites each need
a proof that they keep the tree's meaning; the fallback is cheap (text
kept as written lexes the same, part of B).

The engine proof (A's suffix half) also needs a well-formedness predicate
on documents, since the engine is only safe on documents built the way
the rules build them: a group's `hard` flag must be `forcesBreak` (as
`Doc.group` sets it), because `fits` answers "fits" at a `OneLineBelow`
without looking inside it, and a `Flatten` is measured only where a
choice measures it.

### Friction

1. **`W-ARROW-FORALL` fires on every `theorem name ∀ (x: T) …`** in
   `tools/toyfmt` (68 on `Toy.Fmt.Proofs`), the form the proving guide
   uses. Spurious.
2. **Inner `match`es over list patterns with record fields get stuck**:
   `[{ line, .. }]` patterns had to replace `body.single`-style helpers,
   and multi-statement arms were enumerated by hand.
3. **`rewrite … at` needs a local name**, so a proof term is bound with
   `let` before it can be rewritten.
4. **No `Runs` lemmas for `Parse.operators`, `recursiveWith`, `lastRead`
   or `locatedToEnd`.** The first gates layer D.
5. **Peek-based parsers prove by computing**: `rewrite starts` then `rfl`
   reads a `Parse.peek` branch without a lemma.
6. **`omega` can't see through `_` arguments**: a bound passed to a lemma
   with `_` for the bound gives "needs to know the goal"; writing the bound
   out fixes it.

### Part 2 (Fable, 15 Nov 2026): the parser's operators, the engine's comment rule, the lexer's first lemma

A second 3-hour lane, on the three places the plan called risky. Each was
tried far enough to see what its proofs cost; none turned out to need a
new idea, and two needed a small restructuring of the program first.

**Proved** (no open goals, no axioms; each checked to fail when the
program is broken: `Parse.nextLowest` for a left-associative level,
`operatorOf`'s level test):

- Std, `Parse/RunsOperators.sw`: `Parse.runsOperators`. A tree of operands
  and operator items (`Parse.OperatorTree`) that is grouped as
  `Parse.operators` groups (`Formed`: each operator is the item its level,
  associativity and function come from; its left side would not have
  taken it; its right side holds only operators its right operand may),
  whose operands `operand` reads where they stand (`RunsEach`), and after
  which no operator comes, is read back from its items, with the tree's
  value. Any levels and both associativities. By induction on the tree
  down its left side (`runsOperandsPrefix`): reading the left side leaves
  the loop where this operator and its right side continue it. A worked
  instance: `9-1-2*3` is `(9 - 1) - (2 * 3)`.
- Std: `Parse.runsRecursiveWith` (the completeness of `recursiveWith`, as
  `runsRecursive`), `Parse.runsNext`, and `Parse.runsLocatedToEnd`: on
  input a lexeme parser reads lexeme by lexeme to its end,
  `locatedToEnd` gives each lexeme with its offset and length.
- `Syntax/ExpressionProofs.sw` and `Syntax/ItemProofs.sw`,
  `runsExpression`: on tokens that spell an expression at a layout
  (`Spelled`: its tokens in order, each of its kind and allowed by the
  layout, and an item's comments where the parser takes them from: its
  own-line comments above its first token, its trailing comment on its
  comma, or on its last token for the last item) of the parser's shape
  (`Shaped`: a field's target and a call's callee are postfix
  expressions, `-` stands before an operand, operators grouped by
  precedence and chaining from the left), followed by no call, field or
  operator, `expression layout` reads exactly those tokens and gives the
  expression. Covers every expression but `if`, nested to any depth:
  names, numbers, strings, brackets, lists, calls, fields, negation and
  operator chains. `Spelled` and `Shaped` are `False` for an `if`, so the
  theorem says nothing there. `runsExpressionExample` is an instance, the
  six tokens of `f(a) + b`. Std's `Parse.lastReadAfter` (what
  `Parse.lastRead` gives after a read) was needed for the comments.
- `Doc/Proofs.sw`: `lineAfterComment`, `softLineAfterComment`,
  `fillSepAfterComment`: a `Line`, `SoftLine` or fill separator reached
  while a trailing comment waits prints a line break, in a flat group too.
- `Syntax/LexProofs.sw`, `runsWordLexeme`: `lexemeAt` reads a word (a
  letter or `_`, then word characters, up to a character that isn't one)
  as a `WordLexeme`.

**Restructured, with the same behaviour** (the 93 tests pass, goldens and
messages included; the lexer's and parser's speed was not measured here,
each change adds a call per lexeme or operator):

- The engine now tests for a waiting comment at `Line` and `SoftLine`
  itself, as `FillSep` did. `fits` already kept such a group from printing
  flat, so no output changes; but "no code after a comment on its line"
  was a fact about how far `fits` looks ahead (the plan's layer A, the
  half estimated at 2-4 days) and is now three one-line lemmas. What is
  left of layer A is the plain simulation: `print` is one of the
  width-free readings.
- Std's `operandsFrom`, `operatorsFrom` and `locatedToEndFrom`, and the
  toy's `suffixesFrom` and `negationsFrom`, call named functions
  (`operandsAfter`, `operatorsAfter`, `nextLowest`, `locatedToEndRound`,
  `suffixesAfter`, `postfix`, `itemsAfter`, `commentsAbove`) where they
  had a `match` or `if` after an effect. A `match` written inside a recursive definition can't be named
  by a lemma (std's `manyRound` exists for the same reason).
- The lexer chooses its lexeme in a pure function (`lexemeStart`), then
  reads it (`readLexeme`). A definition that performs abilities gets no
  equations, and its patterns on character literals don't compute for an
  unknown character; the pure function's generated equations
  (`lexemeStart.eq5: char ∉ [' ', '\n', '"'] → … → isWordStart char →
  lexemeStart [char, ..tail] = Some WordLexeme`) are exactly the facts the
  lexing layer needs.

**What this changes in the plan.** The layers, as they now stand:

| Layer | Left | Lemmas [estimated] |
|---|---|---|
| A, engine | `print` is the text of one reading of the document (each `Line` a space or a break, each choice an option); the comment half is done | 20-30 |
| B, lexing | `lexemeAt` for the other 8 lexemes (strings are the long one); `assemble`'s fold (line starts, columns, comments onto tokens); `Parse.all` from `runsLocatedToEnd`; texts joined and sliced | 50-70 |
| E, rules to tokens (new; was hidden between B and C) | the tokens of any reading of a tree's document spell the tree (`Spelled`), with the columns from layer C and the comments from the comment proofs | 50-70 |
| D, parser | `if` and bodies, blocks (`many1`, the notes above a statement, kept blank lines), statements, declarations, the file | 30-40 |
| WF | the parser gives `Shaped` trees, and the lexer's tokens can be lexed again (a name is a word and no keyword, a string closes) | 50-70, or a run-time walk |
| Glue | `formatDirect`, round trip, idempotence | 10 |

About 220-290 lemmas. This lane proved 78 theorems (22 in std, 56 in the
toy) in about 50 minutes on the clock, most first time; what took longer
was finding each restructuring. Its length was set by the model's context,
not the clock: a lane's worth is about 80 lemmas. At that rate the rest is
3 to 4 more lanes like this one **[estimated, from this lane's measured pace; the
string lexeme, `assemble` and layer E have not been tried]**: days, not
weeks.

**`AsWritten` is the piece that doesn't fit.** A declaration kept as
written is printed as its source text, so the round trip needs: lexing
and parsing that text again, at another offset, gives the same tokens and
again a declaration with a comment out of place. That is a statement
about the whole lexer and parser being unmoved by what surrounds a
declaration, not a read-back from a tree, and is as large as layer D
again. The cheap end state: `formatDirect` skips the re-parse only for a
file with no `AsWritten` declaration, and re-parses the others (a file
with a comment where no rule places one). The real formatter's
left-as-written fallback has the same shape. A decision for Matt.

**For the real formatter**, the expensive std pieces are done once
(`runsOperators`, `runsRecursiveWith`, `runsLocatedToEnd`), layer A is
one engine, and the per-node work is what `runsExpression` shows: about
3 lemmas per node kind in D, and by the comment and layout proofs about
as many again in E. With 94 node kinds against the toy's 17 that is
1,000 to 1,500 lemmas, weeks of lane time at this pace **[estimated, very
low confidence: nothing of the real formatter was tried]**, and its
parser is Rust, so layers B, D and WF would be about a Stitchwort port of
it, or stay a run-time check.

**Friction** (beyond part 1's):

7. **A `match` or `if` after an effect in a recursive definition can't be
   named**, and a lambda in a proof can't hold a `match`
   (`E-MATCH-MOTIVE`), so each such step needs a helper `def` in the
   program. Eight were added here. The error's notes say so clearly.
8. **No equations for a definition that performs abilities** ("stage
   1a"), so a parser that chooses by patterns must keep the choice pure.
9. **`rewrite starts` reaches only the reads a computation has got to.**
   A parser that looks at the input twice (`expressionRule`, then
   `negationsFrom`) is rewritten on one side of the goal and not the
   other. Taking the state apart with a record pattern (`match state with
   | { at = { rest = [token, ..later], … }, … }`) refines every read at
   once (`chainRuleRun`).
10. **`rewrite` with a rule about a call that appears only after an
    earlier one computes** (`operatorOf layout 2 sign`, reached once level
    1 says `None`) finds nothing; split the value first, then rewrite as
    many levels as that case reads (`operatorFound`).
11. **Constructor order of a nested `∃`**: `Spelled`'s arms are four or
    five `∃`s and as many `∧`s deep, matched as `Witness a (Witness b
    (Both … ))`; a record-shaped proposition would read better.
12. `std_library::the_standard_library_passes_its_own_tests` fails on this
    branch at "Args.run: a mistake fails with the complaint, and prints
    nothing" (an `Args` test, from SW-3403's exit codes by the look of it;
    nothing here touches `Args`), which hides whether the tests after it
    pass.


### Part 3 (Fable, 15 Nov 2026): the rest of the parser's read-back, the lexemes, `lex`

A 1-hour lane, used for about 35 minutes of the clock: 67 theorems (4 in
std, 63 in the toy), almost all first time. D3618 came in at the start
(no `AsWritten`) and its design during the lane (a comment slot on every
token), so nothing here proves where comments sit beyond what the
parser's own functions say (`notedStatement`, `notedDeclaration`,
`trailingFor`), and the `AsWritten` case is not proved.

**Proved** (no open goals, no axioms; `stitchwort audit Toy` and `audit
Std.Parse` clean but for the search's "no input made the hypotheses
true" on state-shaped hypotheses):

- `Syntax/BlockProofs.sw`, each construct given its parts: `runsIf`
  (keyword, condition, `then`, body, `else`, body), `runsElse`,
  `runsKeyword`, `runsBodyInline` and `runsBodyBlock` (which of the two
  `body` reads is decided by the next token starting a line deeper),
  `runsLineLet`, `runsLineBare`, `runsStatement`, `statementDeclines`
  (a block ends at a token that doesn't start a line at its column),
  `runsBlock`, `runsDeclarationValue`, `runsDeclarationFunction`,
  `runsParameters`, `runsNoParameters`, `runsDeclaration`,
  `declarationDeclines`, `runsSourceFile`, and `parseReads`: a source that
  lexes, whose tokens `sourceFile` reads to the end as a file, parses to
  that file.
- Tied together from a spelling:
  - `runsExpression` now covers an `if` whose branches are each one
    expression (`Shaped` and `Spelled` have an `if` arm, `ShapedInline`
    and `SpelledInline`), nested anywhere, in brackets too.
    `runsIfExample`: the six tokens of `if a then b else c`.
  - `runsBody` and `runsBodySpelled`: tokens that spell a body after `=`
    (`SpelledBody`: one expression, or a block of `let` and expression
    statements at the column of its first token, to any depth, each
    statement's first token carrying the notes above it) read back
    through `body` and `bodyFuel`; the block's fuel is shown to be enough.
  - `runsValueSpelled`, `runsFunctionSpelled`: a whole declaration.
- `Syntax/LexProofs.sw`: `lexemeAt` reads each of the other eight
  lexemes (`runsSpacesLexeme`, `runsLineBreakLexeme`, `runsCommentLexeme`,
  `runsDigitsLexeme`, `runsPunctuationLexeme`, `runsStrayLexeme`,
  `runsSymbolsLexeme`, `runsStringLexeme` with an instance); `lexReads`:
  a source `lexemeAt` reads lexeme by lexeme to its end, whose slices add
  up to it, lexes to those lexemes located and the tokens `assemble`
  makes of them; and what each lexeme does to the tokens being assembled
  (`addSpaces`, `addLineBreak`, `addOwnLineComment`,
  `addTrailingComment`, `addCode`).
- Std: `Parse.runsFromRun`, `runsFromWhole`,
  `runsFromWithFinalLineBreaks`, `runsFromAll`: the runners' completeness
  from the start state, for a parser whose value depends on where it
  starts (`locatedToEnd`'s offsets). `lexReads` needed them.

Checked to fail on a broken program: a statement accepted at a deeper
column fails `runsStatement` and `statementStops`. The lexeme lemmas take
the lexer's pure choices (`lexemeStart`, `operatorNext`, `segmentStart`)
as hypotheses, so breaking those functions does not fail them; the
lemmas that discharge the hypotheses (`wordLexemeStart`,
`digitsLexemeStart`) would.

**Restructured, same behaviour** (93 tests pass): the parser's inline
body, bare statement, a statement's line and its notes, a declaration's
line and its notes, and the file's end are functions of their own
(`inlineBody`, `bareStatement`, `statementLine`, `notedStatement`,
`declarationLine`, `notedDeclaration`, `fileEnd`, `fileOf`); the lexer's
operator run and string piece choose in pure functions (`operatorNext`,
`segmentStart`) and the string's closing quote is `stringClosed`.

**Not done, and what it needs:**

1. **An `if` with a block for a branch.** The block's last statement is
   followed by tokens outside the `if` (`else`, or whatever follows the
   whole expression), and its layout is `InStatement column start` with
   `start` the offset of the statement's first token: `Layout.allows` lets
   a token through if its offset is `start`. So "the next token is not
   part of this statement" needs the tokens' offsets to differ, which
   `Spelled` does not say (it has no `rest`). Either `Spelled` gets the
   tokens that follow, as `SpelledBody` has, or a predicate that the
   following token starts a line at or left of the statement with an
   offset none of the expression's tokens has. About 20-30 lemmas, mostly
   lists of offsets. `SpelledBody`'s block arm already states the
   condition per statement (`EndsExpression (InStatement column
   first.offset) (later ++ rest)`), for layer E to supply.
2. **The file from its spelling**: `runsSourceFile` takes the rounds; a
   `SpelledFile` like `SpelledLines` (declarations at column 0, the notes
   above each, the end notes) is the same induction again, about 10
   lemmas. Left because the notes are what D3618 changes.
3. **`covers`** in `lexReads` is a hypothesis: the lexemes' slices joined
   are the source. It needs std lemmas about `Text.slice` and
   `Text.concat` (none found).
4. **A digit is no word start**, a hypothesis of `runsDigitsLexeme`: a
   fact about `Char.isAsciiDigit` and `isAsciiLetter` for an unknown
   character.
5. **Layer E** was not started.

**Under D3618's design** (a comment slot on every token, no `AsWritten`,
no note lines): the structural lemmas keep their statements (`runsIf`,
`runsElse`, `runsKeyword`, `runsBodyBlock`, `runsLineLet`, `runsBlock`,
`statementDeclines`, `declarationDeclines`, the parameters, the
declarations' lines, every lexeme lemma, `lexReads`, the std lemmas).
These change with the tree: `runsBareStatement`, `runsInlineBody`,
`runsBodyInline`, `bodyOf` and `SpelledInline` (a bare statement's
`trailingFor`); `runsStatement`, `SpelledLines`, `linesRun`,
`firstBlank` and `groupSome` (the notes above a statement, kept in
`pending`; with comments on tokens the block's lines are just its
statements and `linesRun` loses its hardest third); `runsDeclaration`,
`runsValueSpelled`, `runsFunctionSpelled` (`notedDeclaration`, which
holds the `AsWritten` test); `runsSourceFile` (`fileOf`'s end notes);
`addOwnLineComment`, `addTrailingComment`, `addCode` (the token's
`above` and `trailing`).

**Re-estimate** [estimated, from this lane's measured pace of about 2
theorems a minute where the technique is known]:

| Layer | Left | Lemmas |
|---|---|---|
| D, parser | `if` with a block branch; the file from its spelling; redo of the comment-bearing lemmas after lane T | 40-60 |
| B, lexing | `covers` (std `Text`), `assemble` over a whole line and file (columns, line starts), texts to lexemes | 40-60 |
| A, engine | unchanged from part 2 | 20-30 |
| E, rules to tokens | untried | 50-70 |
| WF | unchanged | 50-70, or a run-time walk |
| Glue | unchanged | 10 |

Two to three more lanes of this size, best run after lane T has changed
the tree, since D's comment-bearing lemmas, E and WF are all stated
against it.

**Friction** (beyond parts 1 and 2):

13. **A `let (a, b) := f x` after which the pair doesn't compute** (a
    fold over an unknown list) blocks `rfl`; the lines were moved into
    functions (`notedStatement`, `fileOf`) so a theorem can name the
    result.
14. **A helper's call nested in a record literal elaborates with one
    more bind** than `let line := helper …` then the record; the
    program was written the second way.
15. **`rewrite starts` reaches the first read only** (as friction 9):
    in `runsDeclaration` the second use of `start.rest` is not rewritten,
    which is what the proof needs there, but only by luck.
16. **`match h: e with` already replaces `e` in the goal**; a `rewrite h`
    after it finds nothing (the error says so, well).
17. `test` is a keyword and can't be a parameter name.
18. The audit's search reports "no input made the hypotheses true" for
    any theorem whose hypothesis is about a parser state.

### Part 4 (Fable, 15 Nov 2026): what the parser guarantees (WF), and the readings (layer A)

A 1-hour lane, on the two untried layers. WF's shape half is proved, not
checked; layer A's refinement is done; layer E was designed against the
new `Reads` but none of it is proved.

**Proved** (no open goals, no axioms; `audit Toy`: 305 theorems, 0
failed, the same 9 warnings as before; `audit:touched -- Std.Parse`
clean):

- Std, `Parse/ReadsOperators.sw`: the soundness half for
  `Parse.operators`, the converse of `runsOperators`.
  `Parse.readsOperators`: an invariant of the values `operators` builds.
  Given `chain lowest highest` (what the loop holds on its left while it
  reads operators of levels `lowest` to `highest`) and `grouped lowest`
  (what comes of operators of level `lowest` or tighter), if every operand
  is `atom`, an atom is a chain, a chain is grouped, and joining a chain
  by an operator in its range to a right side grouped as the operator's
  associativity asks gives a chain up to that level, then whatever
  `operators` gives is `grouped 0`. Also `Parse.readsRecursiveWith` (as
  `readsRecursive`, per argument) and `Parse.readsThenOf`
  (`readsThen` with the two parsers named).
- `Syntax/ShapeProofs.sw`, **`parseShaped`**: `parse source = Ok file →
  ShapedFile file`, for every source. Every expression in every tree the
  parser gives is `Shaped` (operators grouped by precedence and chaining
  from the left, a call's callee and a field's target postfix, `-` before
  an operand), in every declaration, block and `if` branch. On the way:
  `givesExpression` (`expression layout` gives a `Shaped` expression,
  whatever the tokens), `givesChain` (by `readsOperators`), `givesAtom`,
  `givesSuffixes`, `givesNegations`, `givesItems`, `givesBodyFuel`,
  `givesBlock`, `givesStatement`, `givesDeclaration`, `givesSourceFile`.
  So the read-back theorems' `Shaped` hypothesis needs no run-time walk.
- `Shaped` now covers an `if` with block branches (`ShapedBody` in its
  `if` arm; `ShapedInline` is gone, `SpelledInline` already said the
  branch is one expression).
- `Doc/Readings.sw`, layer A's refinement, **`printIsReading`**: `print
  doc width` is the text of a reading, at every width. A reading
  (`StepsTo`, `Reads`) is a run of the printer in which each question
  asked of the width is answered either way: a fill separator is a space
  (only with no comment waiting) or a break, a group goes flat (only with
  no hard break in it) or breaks, a broken fill's first item goes either
  way, a broken choice takes any option (`IsOption`). Every other step is
  the printer's own (`printDoc`, which for those nodes doesn't look at
  the width). `stepIsReading`, `runIsReading`. With the budget and
  comment lemmas of parts 1 and 2, layer A is finished: nothing about
  `fits` is left to prove, and changing `fits` (the follow-up that makes
  it less conservative after a comment) can't break anything beyond the
  budget proofs.

**Restructured, same behaviour** (98 tests pass, goldens and messages
included): `atomOf`, `callAfter`, `fieldAfter`, `functionLine`,
`valueLine` and `noteStep` are functions of their own (a call per atom,
suffix, declaration and comment); `Printer.start` names the empty
printer.

**Checked against a broken program:** with `Parse.nextLowest` giving a
left-associative operator its own level, std's `runsOperatorsExample`
fails and an `omega` goal fails with it; the run stopped at std's error,
so whether `chainStep` is the `omega` that fails was not isolated. No
other mutation was tried in this lane.

**What made WF cheap.** The value-only form: a spec `taken value => P
value` ignores what was read, so each parser needs one lemma, `Gives
parser P`, and the combinators are three (`givesThen`, `givesDone`,
`givesOptional`). A parser that looks ahead (`peek`) is proved from the
raw run: `match e: state.at.rest with`, then each arm's hypothesis has
computed to that arm's parser, and the lemma for it applies. Arms that
fail (`Parse.expected`, `stop`) are left out: the checker sees their
hypothesis is `Err … = Ok …`. 67 theorems in `ShapeProofs.sw`, a few
check runs.

- `Syntax/LexProofs.sw`, `digitIsNoWordStart`: a digit is no letter and
  not `_` (two `omega`s), so `runsDigitsLexeme` lost that hypothesis.

**WF, what is left** (the texts, not the shape):

1. A `Name`'s text is a word and no keyword, a `Number`'s digits, a
   `Str` closes, a comment is `--` to the line's end with no line break:
   facts about the lexer's tokens (`Parse.readsLocated`,
   `Parse.tokensReads` are the std lemmas), carried through the parser by
   the same `Gives` lemmas with a stronger predicate (each tree text is
   some token's text). About 30-40 lemmas [estimated from this lane's
   pace].
2. Bodies: a body is one `Bare` or a block whose first line has no blank
   above it and whose last line is a statement. `givesBlock` and
   `shapedNoted` have the structure; about 10 lemmas.

**Layer E, as it now stands** (designed, not started). State it against
`Reads`: for every tree with `ShapedFile` and lexable texts, and every
`final` with `Reads (Printer.start width) fuel [Print 0 Break
file.layout] final`, the pieces `final.flushSuffixes.out` are lines of
token texts whose tokens spell the tree (`Spelled`, `SpelledBody`,
`SpelledLines`). The proof is an invariant of `StepsTo` over the
printer and its work list; the pieces are already separate in `out`
(token texts, `" "`, `"\n"`, indentation, comments), so layer B's
remaining half (`assemble` over a line) is a statement about that list,
not about characters. The comment lemmas (`textAfterComment`,
`spacesAfterComment`, `continuationDeeper`) and layer C's scans are the
facts the invariant uses. Untried, so still the estimate with the least
behind it: 50-70 lemmas.

**Re-estimate** [estimated; this lane proved 80 theorems (7 in std, 73
in the toy), almost all on the first or second check]:

| Layer | Left | Lemmas |
|---|---|---|
| A, engine | nothing | 0 |
| WF | token texts, body structure | 40-50 |
| D, parser | `if` with a block branch; the file from its spelling | 30-40 |
| B, lexing | `covers`, `assemble` over pieces | 40-60 |
| E, rules to tokens | all of it | 50-70 |
| Glue | `formatDirect`, round trip, idempotence | 10 |

Two lanes: one for E with B's `assemble` (they share the pieces
invariant), one for the rest of WF, D and the glue. `formatDirect` is two
lanes away, not one, because E is still untried.

**Friction** (beyond parts 1 to 3):

19. **`Parse.readsThen` infers its two parsers from the goal** and fails
    with a long conversion error where the goal only computes to `j
    (p())` (a `let x := f (effect())`, or a branch reached by a rewrite);
    `readsThenOf` takes them as arguments. It does infer through a
    `match` after an effect and a `let (a, b) :=`, which a lambda in a
    proof can't write, so both are needed.
20. **`let y := pure (effect())` is two binds**, and `bind (bind p f) k`
    is not `bind p (x => k (f x))` by computation: `parametersOf
    (Parse.optional parameterList)` had to be read as one parser.
21. **A definition whose `match` is on a `let` after a peek** doesn't
    compute at fuel `Zero` (`suffixesFrom`), where one that matches
    `fuel, peek()` does (`negationsFrom`, `operatorsFrom`); the zero case
    repeats the whole case split.
22. **`W-LAMBDA-SHADOW` on `read`** (`Files.read`) for every spec
    written `(read value => …)`, the spelling std's own lemmas use.
23. `cases` proves `expr.isPostfix = True → expr.isOperand = True` but
    not `expr.isOperand = True → expr.chainLevel = 7`; a `match` with
    the impossible arms left out does.

### Part 5 (Fable, 15 Nov 2026): the words of every reading (layer E's first half), `covers`, the column

A 1-hour lane on layer E and layer B's `covers`. Layer E's token-order
half is proved end to end (engine and rules); its positions half
(columns, line starts, what may stand next to what) is designed below
and not started, so there is still no `formatDirect`.

**Proved** (no open goals, no axioms; `audit Toy`: 432 theorems, 0
failed; `audit:touched -- Std.Parse` and `-- Std.Text` clean):

- Std: `Text.sliceMiddle` (in a text made of `before`, `middle`, `after`,
  the slice after `before` as long as `middle` is `middle`);
  `Parse.locatedStepsSlices` and **`Parse.locatedStepsCover`**: the
  slices of a source at the places of the steps that read all of it,
  joined, are the source.
- `Syntax/LexProofs.sw`, `lexemesCover`: the lexemes of steps that read
  all of a source cover it, so **`lexReads` lost its `covers`
  hypothesis** (layer B's item 3 of part 3).
- `Doc/Words.sw` (44 theorems), layer E's engine half.
  **`readingWords`**: a reading with the steps to finish writes the work
  list's words after the printer's, in order, whichever way groups,
  fills and choices go. A word is a piece of output that isn't layout
  (`isLayout`: spaces or a line break); the printer's words are those
  written and then the trailing comments waiting. It asks that every
  option of each choice has the same words (`Uniform`).
  **`printWords`**: so `print doc width` is pieces joined whose words are
  `doc.words`, at every width. On the way: `writeWords`, `newlineWords`,
  `flushWritten` (each printer operation), `stepWords` (a step moves
  words from the work list to the printer), `readingLighter` (a
  reading's steps weigh the work list down as the printer's do, so a
  reading ends within `print`'s budget).
- `Fmt/WordProofs.sw` (57 theorems), layer E's rules half.
  **`fileWrites`**: the document the rules build for a file is `Uniform`
  and its words are those of the file's pieces (`SourceFile.pieces`:
  each token's own-line comments, its text, its trailing comment, in the
  source's order; the last item and parameter without a comma, as
  `itemDocs` prints them). **`printPieces`**: so a file printed at any
  width is its pieces with only layout between them: no token or comment
  lost, repeated or moved. `exprWrites`, `statementWrites`,
  `declarationWrites` and one lemma per rule, by the combinators
  `writesCons`, `writesConcat`, `writesChoiceTwo`/`Three`, `writesJoined`,
  `writesChain`.
- `Doc/Columns.sw` (23 theorems). **`readingTracks`**: through every
  reading of documents whose chunks have their texts' widths and are no
  line breaks (`Measured`), the printer's `column` is the number of
  characters on the last line of `out`, a line with indentation owed is
  empty, and a line marked as only started is empty (`Tracks`). So the
  column the printer has when it puts a chunk (the indentation owed, or
  `column`) is the chunk's column in the text, which is what `assemble`
  computes for the token: the bridge the positions half needs.

**Checked against a broken program:** with the comma dropped from
`itemDocs`, `itemDocsWrite` fails; with `write` putting text at a line
start before a waiting comment (as it did), `writeWords` fails; with
`put` adding one to the column, `putTracks` fails.

**The program changed in three places**, goldens, probes and messages
the same (98 tests pass):

1. `Printer.write`: text after a waiting trailing comment always starts
   a new line, also when the comment waits at a line start (it used to
   put the text first, so the comment moved after it). The rules never
   get there (a `LineSuffix` follows its token's text), but "a comment is
   written before the text after it" now holds of every document, with no
   condition, which is what lets `readingWords` say "in order".
2. `trimSpaces` drops the pieces of spaces at the end of a line and no
   longer cuts spaces off the end of a chunk. The rules' spaces are
   chunks of their own, so nothing they print changes; one engine test
   built `"f + "` as one chunk and now builds `"f +"`, `" "`. Without it
   `readingWords` would need "no chunk ends in a space" of every
   document.
3. `Printer.flushOne` and `declarationLines` are functions of their own
   (the fold's step, and the file's lines without `withIndex` and a
   tuple lambda), so lemmas can name them.

`textAfterComment` and `spacesAfterComment` lost their "after code"
hypothesis with change 1.

**What made it cheap.** A reading invariant has the same shape every
time: a predicate on documents carried along the work list (`Uniform`,
`Measured`), one lemma per printer operation, one `match` over the
command and the document for `StepsTo` (26 arms, most `rewrite steps in`
and the operation's lemma), and an induction over `Reads`. The third
(`Columns.sw`) took a quarter of the time of the first. On the rules
side, `Writes doc pieces` composes like `Keeps` of layer C, and the
pieces are defined in the association the rules build, so no lemma
re-brackets an append.

**Layer E, what is left: positions.** Three facts about every reading,
each an invariant of the same shape, then the lexing glue:

1. **What stands next to what** (the munch conditions, and comments
   ending their lines). Designed, engine side: the printer's *edge* is
   what the next text would follow on its line: `Fresh` (a line start),
   `After word spaced`, or `Waiting` (a trailing comment waits, so the
   next text starts a line). A predicate on the work list in
   continuation style, `doc.joins edge then`, lists every edge the engine
   can leave: a chunk asks `follows` of the edge and goes on from
   `After text`; a `Line` or fill separator goes on from the spaced edge
   and from `Fresh`; a `SoftLine` from the edge and from `Fresh`; a
   choice from every option; a `LineSuffix` asks `follows` with a space
   and is refused while another waits (two would print as one comment).
   The invariant: the predicate holds of the printer's edge and work
   list, every adjacent pair in `out` satisfies `follows`, a line marked
   as started has a `Fresh` edge, and a waiting comment fits the edge it
   will be flushed at (with "indentation owed means the line is only
   started", which `Tracks` has). No join of abstract states is needed,
   because the predicate quantifies over the outcomes instead of
   approximating them; it does need "a weaker continuation still holds"
   (one induction over the document), since the work list's predicate
   and a `Concat`'s or `Fill`'s agree only up to their continuations.
   Two engine facts make it exact: text after a waiting comment always
   breaks first (change 1 above), and a line break flushes the comments
   and writes `"\n"` in one step. About 35 lemmas for the engine, 40 for
   the rules (each expression form: which edges it may start at, which it
   ends with), and then `LexemesRun` from `follows` with the lexeme
   lemmas of part 3 (adjacent pieces of spaces are one `Spaces` lexeme).
   It also gives "an own-line comment's chunk is followed by a line
   break", which the rules owe (`CommentEnd`, the `HardLine` after a
   note) and which needs WF's "a block doesn't end in a note".
2. **Where each token is**: with `readingTracks`, a positioned trace
   (each word with the `atLineStart` and column it was put at), and
   `assemble` over the pieces giving the same `startsLine` and `column`
   (layer B's last part; `addCode` and the other four step lemmas of
   part 3 are its cases).
3. **Layer C read back**: the scans of `LayoutProofs.sw` say which lines
   may start at a statement's column, but about the document, not a
   reading. Connecting them is the same continuation-style predicate as
   item 1 over the printer's `owed` and `lineIndent`.

Then the tokens spell the tree (`Spelled`, `SpelledBody`, `SpelledLines`
from the three facts and `printPieces`), which is where WF's token texts
come in.

**Re-estimate** [estimated; this lane proved 129 theorems (3 in std) in
about 30 minutes of checking and writing, nearly all on the first or
second check]:

| Layer | Left | Lemmas |
|---|---|---|
| A, engine | nothing | 0 |
| B, lexing | `LexemesRun` from the pieces; `assemble` over them | 30-40 |
| E, rules to tokens | adjacency (75), positions (25), layer C read back (30), spelling the tree (40) | 160-180 |
| WF | token texts, body structure | 40-50 |
| D, parser | `if` with a block branch; the file from its spelling | 30-40 |
| Glue | `formatDirect`, round trip, idempotence | 10 |

Three lanes at this lane's pace: adjacency with `LexemesRun`; positions,
`assemble` and layer C's read-back; then spelling the tree with WF, the
rest of D and the glue. Part 4's "two lanes" counted E as 50-70 lemmas;
E's first half alone was 100, small ones.

**Friction** (beyond parts 1 to 4):

24. **A `match` on an expression rewrites it everywhere, also inside the
    lemma you meant to apply afterwards**: matching `printer.suffixes`
    computed the goal past the form `putWritten` states. Matching the
    test the program makes (`printer.suffixes.isEmpty`) and deriving
    `suffixes = []` from it keeps the goal readable.
25. **Arguments written out inside an arm aren't refined by the
    `match`** (E-TYPE-MISMATCH names it): `_` for them, or a helper
    lemma that takes the scrutinee's equation.
26. **`True` as a proposition is proved by `rfl`**, not `Trivial` or
    `True.intro` (it is the test fact `True = True`); the error says "no
    reading" without saying which proof it wants.
27. **No projections for `∧`**: `(match both with | Both first _ =>
    first)` inside an arm needs its own brackets, or the outer `match`
    takes its arms.
28. `&&` groups to the right (`a && (b && c)`); the error showed it.
29. The audit warns "no input made the hypotheses true" for
    `spacesAfterComment` (a text of spaces while a comment waits);
    `spacesAfterCommentExample` is an instance.

### Part 6 (Fable, 15 Nov 2026): what the printer puts next to what (engine), lexing from pieces

A 1-hour lane on layer E's adjacency half and layer B's lexing from the
pieces. The engine's side of adjacency, the lexer's side of "pieces lex
to themselves" and the glue between them are proved, ending in
`joinedLex`: a document that joins, printed at any width, lexes to its
pieces. The rules' side (that the document the rules build for a file
does join, which chunks they put next to which) is designed below and
not started, so "the printed text lexes to the file's tokens" still has
that hypothesis, and there is no `formatDirect`.

**Proved** (no open goals, no axioms; `audit Toy`: 533 theorems, 0
failed, the 10 warnings all on theorems of earlier parts):

- `Doc/Joins.sw` (59 theorems), layer E's adjacency, engine half.
  **`printJoins`**: for a `Uniform` document that joins from a line
  start (`Joins follows doc (Plain None) (after => True)`), at every
  width, `print` is pieces joined where no piece is empty, the pieces'
  words are the document's, and each piece that isn't layout is followed
  by nothing, by a line break, or by a piece `p` with `follows piece (gapOr
  p)` (`Pairs`; `gapOr` turns spaces of any length into one space).
  `follows` is any relation the caller picks; the engine asks nothing of
  it. **`readingJoins`** is the same of every reading, however far it
  gets. On the way: `stepJoins` (one step keeps the printer `Sound` and
  hands the edge it leaves to the work list), one lemma per printer
  operation (`putSound`, `newlineSound`, `writeHolds`, `lineStartHolds`,
  `blankHolds`, `suffixHolds`, `flushedPairs`, `finalPairs`), and
  `joinsWeaker` (a weaker continuation still holds; with `allWeaker`,
  `fillWeaker`, `sepsWeaker`, `optionsWeaker`).
- `Syntax/StandProofs.sw` (15 theorems), layer B. `Stands lexeme read
  rest`: `read` is shaped as that lexeme and `rest` doesn't continue it
  (`StopsAt`: `rest` is empty or its first character fails the lexeme's
  test; a comment stops only at a line break or the end).
  **`standingRun`**: steps that each stand before the rest are
  `Parse.LexemesRun lexemeAt`; **`standingLex`**: so a source made of
  them lexes to them, with the tokens `assemble` makes. What the printer
  writes stands: `operatorStands` (each of the twelve operators before
  text that starts with no operator character), `definesStands`,
  `keywordStands`, `signStands`; and `minusBeforeMinus`: a `-` straight
  before a `-` does not stand (bug 1 of part 1, as a theorem).
- `Fmt/PieceProofs.sw` (27 theorems), the glue. `standsBefore word
  next`: `word` is read whole, as the lexeme it starts with
  (`lexemeOf`), when `next` comes straight after it, whatever comes
  later; `Proper piece`: a piece that isn't layout is read whole at the
  end of the text and before a line break. **`piecesStand`**: printed
  pieces (the last first) with `Pairs standsBefore` and all `Proper`
  are, as steps (`stepsOnto`: neighbouring pieces of spaces one `Spaces`
  step, a line break a `LineBreak`, a word the lexeme it starts with),
  `StepsStand`; **`piecesLex`**: so their text lexes to those steps.
  **`joinedLex`**: for a `Uniform` document with `Joins standsBefore doc
  (Plain None) (after => True)` whose words are all `Proper`, at every
  width, `print doc width` is `pieces` joined, the pieces' words are the
  document's, and `lex` of it is `Ok` with the pieces as lexemes and the
  tokens `assemble` makes of them. `joinedLexExample` meets the
  hypotheses for `f(`. On the way: `standsNoSpace` (only a `Spaces`
  lexeme starts with a space), `gapConsStand`, `addStands`, `joinedChars`
  (the characters of pieces joined, from std's `Text.concatToList`).

**Checked against a broken program:** with `write` putting text after a
waiting comment on its line, `writeHolds` fails (with part 5's
`writeWords`); with `flushOne` leaving out the space before the comment,
`flushOnePairs` fails.

**The design as built** (it differs from part 5's sketch in three
places).

- The edge is `Plain touching` (no comment waits; `touching` is the last
  piece if it isn't layout) or `Waiting`. `Fresh` and "after spaces" are
  both `Plain None`: nothing is asked of what follows layout.
- One relation, not two. `follows word next` covers a chunk after a
  chunk and a space after a chunk (`follows word " "`), so "a comment
  ends its line" is just that nobody can prove `follows comment " "` or
  `follows comment text`: after an own-line comment's chunk only a line
  break joins. A line break after a piece asks nothing.
- `Joins` over-approximates in one place: a `Line` asks `follows word
  " "` whether or not its group is flat (modes aren't tracked). The
  rules never put a `Line` after a comment's chunk, so nothing is lost.
- What `Sound` carries between steps: `Pairs` of the output; indentation
  owed only at a line start; a line marked as only started has nothing
  on it (`Fresh`: the output is empty or ends in a line break; `Tracks`
  of part 5 says the same by widths, this one needs no `Measured`); at
  most one comment waits, it isn't empty, and a space may follow the
  output once its trailing spaces are dropped (`trimmedReady` gets that
  from `Pairs`, since spaces after a word already asked `follows word
  " "`).
- **Two waiting trailing comments are refused**: `SuffixJoins` is
  `False` at `Waiting`. So the rules' half can only be proved for trees
  where no token has both a trailing comment and a next token whose
  trailing comment arrives before a line break, which is the open point
  from part 5 for the WF lane (don't build on the opposite).
- An empty trailing comment is refused too (`Joins` asks
  `comment.isEmpty = False`): an empty piece would hide what stands
  next to what.

**What is left of "the printed text lexes to the file's tokens".**

1. **The rules' half of adjacency** (about 40 lemmas, as part 5
   counted): `Joins standsBefore file.layout (Plain None) (after =>
   True)`, with `standsBefore word next := ∀ later => Stands (lexemeOf
   word) word.toList (next.toList ++ later)` and `lexemeOf word` the
   lexeme `lexemeStart` finds. Per expression form: from which edges it
   joins and which it leaves (`Plain (Some lastToken)` or `Waiting`). The
   pairs the rules make without a space are few: a last token before
   `(`, `)`, `,`, `.`, `]`; `(` and `[` before a first token or the
   closer; `.` before a name; `-` before an operand that doesn't start
   with `-` (`operatorStands` with `startsWithMinus`). Everything else is
   `follows token " "`. Needs WF's token texts (a name is a word, digits
   are digits, a string is a string, a comment starts with `--` and has
   no line break) to turn "a name" into `Stands WordLexeme`. A chunk
   whose text is a variable needs `text.isEmpty = False` to compute
   `WriteJoins`; a helper lemma per token class will do.
2. **`Proper` of the file's pieces**: each token's and comment's text
   stands at the end of the text and before a line break. The same WF
   token texts as item 1, a lemma per token class.
3. Then `joinedLex` on `file.layout` (with `fileWrites` for `Uniform`
   and the words) gives `lex (file.print width).text = Ok` of the
   pieces as steps, and `assemble` over those steps is the positions
   half (`readingTracks` for the columns; which steps are `LineBreak`s
   needs the layout pieces, so the positioned trace of part 5's item 2).

**Re-estimate** [estimated; this lane proved 101 theorems in about 30
minutes of the clock, all but eight on the first check]:

| Layer | Left | Lemmas |
|---|---|---|
| A, engine | nothing | 0 |
| B, lexing | `assemble` over the steps | 15-20 |
| E, rules to tokens | adjacency, rules half (40) and `Proper` (10), positions (25), layer C read back (30), spelling the tree (40) | 140-150 |
| WF | token texts, body structure, no two waiting comments | 40-50 |
| D, parser | `if` with a block branch; the file from its spelling | 30-40 |
| Glue | `formatDirect`, round trip, idempotence | 10 |

Still three lanes at this pace: (1) the rules' half with WF's token
texts, ending in "the printed text lexes to these steps" with no
hypothesis but WF;
(2) positions, `assemble` and layer C's read-back; (3) spelling the
tree, the rest of D and the glue.

**Friction** (beyond parts 1 to 5):

30. **`False` as a proposition is `False = True`**, so an impossible
    arm is `Void.exfalso (Bool.falseNotTrue never)`, not `Void.exfalso
    never`; the error says so.
31. **A function with character-literal patterns doesn't compute on an
    unknown character** even when a test on it is known; its equation
    lemmas (`operatorNext.eq2`, `lexemeStart.eq8`) do the work, and a
    wrong argument's error prints their whole signature, which is how
    they were found.
32. **Two constructors named `Clear`** (the edge's, and layer C's
    `Scan.Clear`) met in `Toy.Fmt.Proofs`: the error names both; the
    edge's is now `Plain`.
33. **A term written inside a `match` arm isn't refined, but every
    hypothesis in scope is**, so a lemma that takes the unrefined
    hypothesis can't be called there (friction 25 from the other side):
    the lemma was restated to take only the parts the `match` doesn't
    touch (`wordStands`).
34. **A `let` with a stated type computes the type before `rewrite`
    looks**: `lexemeStart ([' ', ..others] ++ rest) = …` had already
    become `Some Spaces = …`; `Eq.cong` and `Eq.trans` instead.
35. **Continuation-style predicates just work**: `Joins` recurses under
    a lambda (`after => JoinsAll follows rest after next`) through four
    mutual definitions, and the termination checker and `rfl` took all
    of it. `match e, hypothesis with` rewrites `e` inside the
    hypothesis also through an unfolded definition (`printer.edge`).

### Part 7 (Fable, 15 Nov 2026): every rule joins; a parsed body ends in a statement

A 45-minute lane on the rules' half of adjacency, `Proper`, and what of
WF could be had without new std lemmas. The rules' half and `Proper`
are proved, so "the printed text lexes to the file's pieces" now has one
hypothesis, `LexicalFile file`, which says what the parser guarantees.
Of that hypothesis, the structure part (a body ends in a statement) is
now proved of every parsed tree; the token-text part (a name is a word,
and so on) is not, so the theorem is not yet stated from `parse source =
Ok file` alone, and there is no `formatDirect`.

**Proved** (no open goals, no axioms; `audit Toy`: 671 theorems, 0
failed, the 10 warnings all on theorems of earlier parts):

- `Fmt/TextProofs.sw` (23 theorems). What the lexer's texts are, as
  predicates on a text: `IsWord` (a letter or `_`, then word
  characters), `IsName` (a word that spells no keyword), `IsDigits`,
  `IsString` (plain runs and escapes between quotes, closed whatever
  follows), `IsComment` (`--`, then no line break). `Ends word`: `word`
  is read whole, as the lexeme it starts with, before anything that
  starts with no word character, digit or operator character (`Shut`).
  **`wordToken`, `digitsToken`, `stringToken`, `keywordToken`,
  `signToken`, `definesToken`, `operatorToken`**: each such text is
  `Solid` (not empty, not spaces, not a line break) and `Ends`.
  `endsProper`: what `Ends` is `Proper`. `commentSolid`, `commentProper`
  for comments. `wordOpens`, `digitsOpen`, `stringOpens`: these start
  with no operator character, so `-` straight before them is read whole
  (`minusBefore`). `signFree`: a bracket, comma or dot is read whole
  before anything.
- `Fmt/JoinProofs.sw` (60 theorems). `Passes doc pre post`: from every
  edge that satisfies `pre`, `doc` joins (`Joins standsBefore`) and
  leaves an edge that satisfies `post`, and its words are `Proper`. The
  edges: `Loose` (after layout, or a comment waits), `Free` (anything
  may come next: after a bracket or dot), `Meets` (a space, a closing
  sign, a comma, a dot or `(` may come next: after any token), `Admits
  text`, `Left text`, `Enters expr` (the expression's first token may
  come next: it is `-` or starts with no operator character).
  Combinators (`passesCons`, `passesConcat` through `Doc.concat`'s
  filter, `passesFrom`, `passesTo`, choices, `below`, `OneLineBelow`),
  the leaves (`passesText`, `passesSpace`, `passesLine`, `passesSoft`,
  ...), and **`tokenPasses`, `closerPasses`**: a token or closing
  bracket with its comments joins from any edge its text may follow and
  leaves the line at its text or with its trailing comment waiting.
- `Fmt/RuleJoinProofs.sw` (47 theorems). `LexicalFile` (with `Lexical`,
  `LexicalBody`, `LexicalStatement`, `LexicalDeclaration`, ...): every
  name in the tree `IsName`, every number `IsDigits`, every string
  `IsString`, every comment `IsComment`, and every body's last line a
  statement (`ClosedLines`). One lemma per rule: **`exprPasses`** (an
  expression's document passes from `Enters expr` to `Meets`),
  `chainPasses`, `linkPasses`, `ifPasses`, `listPasses`,
  `argumentsPass`, `itemDocsPass`, `fillPasses`, `branchPasses`,
  `elseBranchPasses`, `afterEqualsPasses`, `bindingPasses`,
  `statementPasses`, `linesPass`, `headerPasses`, `declarationPasses`.
  **`fileJoins`**: for a `LexicalFile`, `file.layout` passes from
  `Loose` (so it joins from a line start) and its words are proper.
  **`printedLexes`**: for a `LexicalFile`, at every width, `(file.print
  width).text` is `pieces` joined, the pieces that aren't layout are the
  file's tokens and comments in order, and `lex` of the text is `Ok`
  with the pieces as lexemes (neighbouring spaces as one) and the tokens
  `assemble` makes of them. `lexicalExample` meets the hypothesis for
  the tree of `let x = 1`.
- `Syntax/ShapeProofs.sw`, WF's structure half, proved of the parser.
  `ShapedBody` now also says the body's lines end in a statement
  (`ClosedLines`, with `Coded`: not a comment line), and
  `ShapedDeclaration` that a function's last parameter has no comma's
  comments (`BareLast`). So **`parseShaped`** (`parse source = Ok file →
  ShapedFile file`) now gives both of every parsed tree. On the way:
  `closedNoted`, `closedConcat`, `closedAppend`,
  `closedWithoutFirstBlank`, `withCommasBare`, `parametersBare`;
  `givesBare`, `givesStatementLine`, `givesStatement`, `givesBlock`,
  `givesInline`, `givesParameters` and `givesFunctionLine` carry the
  stronger predicates. Three read-back proofs in `BlockProofs.sw` take
  the stronger `ShapedBody` apart (statements unchanged).

**Checked against a broken program:** with `notedStatement` putting the
statement before its notes, `closedNoted` (and `shapedNoted`) fail; with
`withCommas` giving the last parameter a comma's comments,
`withCommasBare` fails. With `Negate` writing no space before an operand
that starts with `-`, `exprPasses` fails, but at the statement of
`operandPasses` (the document no longer matches), not at a proof step.

**What the rules' half found about the tree.**

- No rule needed `closeAfter`'s exactness: text after a waiting comment
  starts a new line in the engine, so `Joins` holds either way. The rule
  is about where the closer goes, not about lexing.
- Two waiting trailing comments (part 6's open point) never arise: a
  token's text is written between any two `LineSuffix`es, so no WF
  condition was needed for it.
- A body that ended in a comment line would break lexing inside an `if`:
  ` else` would follow the comment on its line. That is why `ClosedLines`
  is in `LexicalBody`; the parser guarantees it (`parseShaped`).
- The last item's comma comments don't matter to lexing (`itemDocs`
  never prints them); they matter to the round trip only.

**WF's token texts: what is left, and how.** `LexicalFile file` for
every parsed file needs three things, none started:

1. *The lexer's tokens have the lexer's texts*: for `lex source = Ok
   lexed`, each token's kind text is `IsName`/`IsDigits`/`IsString` and
   each comment `IsComment`. Std has no soundness lemma for
   `Parse.locatedToEnd` (only the completeness one, `LexemesRun`); it
   needs one whose hypothesis knows the lexeme parser is given the input
   left (`lexeme start.rest`), then the converse of each
   `runs…Lexeme` (what `lexemeAt` read is shaped as its lexeme), `cut`
   as the read characters, and an invariant of `assemble`'s fold. About
   30 lemmas, 5 of them in std.
2. *The parser copies them*: every text in the tree is some read
   token's. `Parse.Reads` gives each parser the tokens it read
   (`taken`), but a spec of the form "if the tokens read are fine, the
   value is" doesn't compose through `readsThen` (the continuation's
   lemma needs the first part's conclusion before its hypothesis is
   known). The form that composes is flat and positive: `value.texts ⊆
   taken.flatMap tokenTexts`, with texts tagged by class (name, number,
   string, comment); then one tree induction turns "all of the tokens'
   texts are fine" into `LexicalFile`. The 67 `gives…` lemmas of
   `ShapeProofs.sw` again with that predicate (about 70), the induction
   (about 15). The `closed…` lemmas above are reusable as they are.
3. *The last item's comma*: `itemsFrom` returns `found.reverse` when its
   fuel runs out, where the newest item had a comma, so "the last item's
   comma comments are none" needs either a count showing the fuel never
   runs out with an item found, or the tree changed so the last item has
   no comma field (a wide change: `Spelled`, `runsItems…`, the dump, the
   rules). Only the round trip needs it.

**Re-estimate** [estimated; this lane proved 138 theorems in about 25
minutes of the clock, all but about ten on the first check]:

| Layer | Left | Lemmas |
|---|---|---|
| A, engine | nothing | 0 |
| B, lexing | `assemble` over the steps | 15-20 |
| E, rules to tokens | positions (25), layer C read back (30), spelling the tree (40) | 95 |
| WF | token texts: lexer (30, 5 in std), parser (70), tree induction (15); last item's comma (10 or a tree change) | 115-125 |
| D, parser | `if` with a block branch; the file from its spelling | 30-40 |
| Glue | `formatDirect`, round trip, idempotence | 10 |

Three lanes at this pace: (1) WF's token texts, ending in
`printedLexes` from `parse source = Ok file` alone; (2) positions,
`assemble` and layer C's read-back; (3) spelling the tree, the rest of
D and the glue.

**Friction** (beyond parts 1 to 6):

36. **A hypothesis named as a function hides it in the statement**:
    `(token: TokenText text)` made `token comments text` in the result
    type "not a function". The error says its type; renaming fixed it.
37. **`cases` runs out on ten character comparisons**
    (`E-CASES-BUDGET` on `isWordStart first → isOperatorChar first =
    False`); ten rewrites with `(symbol == first) = False` did it. The
    digit version went through `cases`.
38. **Two constructors named `Waiting` again** (the edge's and layer
    C's `Scan.Waiting`): every pattern in `Toy.Fmt.Proofs` has to say
    `Edge.Waiting`. One of the two should be renamed.
39. **`W-ARROW-FORALL` now prints 1,609 times** on a check of
    `Toy.Fmt.Proofs` once anything fails, burying the error (friction 1,
    worse); the lane filtered the output with `awk`.
40. **`passesCons _ _` with holes for the documents failed once** where
    the expected type came from `List.map` over a lambda that builds a
    `Doc.concat` (the checker had half-computed the `filter`); writing
    the two documents out fixed it. Elsewhere the holes were fine.
41. **Triples made the rules cheap**: with pre and post as predicates
    on the edge and five combinators, each rule's lemma is the rule's
    document read left to right; 46 lemmas checked with three errors in
    all (a bracket, a duplicate name, a wrong post).

### Part 8 (Fable, 15 Nov 2026): the lexer's half of the token texts

A 45-minute lane on WF's token texts. The lexer's half is proved: from
`lex source = Ok lexed` alone, every token and comment has the lexer's
text (`lexTexts`), with a string's text as its quotes and pieces
(`StringRead`), not yet part 7's `IsString`. The parser's half (the tree
copies the tokens' texts) and the tree induction are not started, so
`printedLexes` still has its `LexicalFile` hypothesis.

**Proved** (no open goals, no axioms; `audit Toy`: 720 theorems, 0
failed, 14 warnings: part 7's 10 and four new ones, `operatorCharPaced`,
`escapeSegmentPaced`, `stringLexemePaced` and `commentTaken`, whose
hypothesis is a run that succeeded or a text that starts `--`, which the
search's random inputs never are; they are narrow, not contradictory,
and `lexTexts` uses all four):

- Std, `Parse/Paced.sw` (19 theorems, new file; the prelude hash
  snapshot gains these names only).
  - `Parse.Paced parser`: run from an honest state, a success leaves an
    honest state whose offset has moved on by what was read (offset plus
    items left is unchanged). `Parse.Reads` says what was read and
    nothing about offsets, and a parser may reset to any mark, so this
    is a property of its own. Lemmas: `pacedPure`, `pacedThen`,
    `pacedIf`, `pacedMark`, `pacedNote`, `pacedStop`, `pacedFatal`,
    `pacedExpected`, `pacedFail`, `pacedSpan`, `pacedNext`,
    `pacedSatisfy`, `pacedChar`, `pacedManyFrom`, `pacedMany`.
  - `Parse.ReadsFrom state parser spec`: `Reads` of one state, so that a
    spec can say what was read in terms of what was there;
    `Parse.readsFromSpan`: `span` reads the longest start whose items
    pass (`readsSpan` says only that they pass).
  - `Parse.LexemesRead spec steps`: each step read something, and `spec`
    holds of the characters that were left, what it read and its value.
  - **`Parse.locatedToEndReads`** (and `locatedToEndFromReads`): for a
    lexeme that reads as `spec` says from each state and keeps count,
    `locatedToEnd lexeme` that succeeded from an honest state read all
    that was left, as `steps`, and gave `Parse.locatedSteps offset
    steps`. **`Parse.allLocatedToEnd`**: the same from `Parse.all input
    (() => locatedToEnd lexeme) = Ok found`: `input.toList` is the steps
    joined and `found = Parse.locatedSteps 0 steps`. The converse of
    `runsLocatedToEnd`.
- `Fmt/LexTextProofs.sw` (49 theorems, new file).
  - The lexer keeps count: `operatorCharPaced`, `stringSegmentPaced`,
    `stringLexemePaced`, `readLexemePaced`, `lexemePaced`.
  - What each lexeme read: `stringSegmentReads`, `stringLexemeReads`
    (`StringRead`: a quote, pieces that are escapes or plain runs, a
    quote), `operatorCharReads`, `readLexemeReads`, **`lexemeReads`**:
    from each state, `lexemeAt` given what is left read the lexeme it
    starts with (`LexemeSpec`), a word, number or comment as the longest
    run of its characters.
  - From `lexemeStart`'s choice back to the first characters:
    `guardedStart` (the later arms as one chain of tests, `charClass`),
    `classOf`, **`wordStartOf`**, **`digitStartOf`**,
    **`commentStartOf`**.
  - **`lexemesRead`**, **`lexRead`**: a lex that succeeded is `steps`:
    the source is their characters joined, the lexemes are the steps
    with their places, tokens and end trivia are `assemble`'s. The
    converse of `lexReads`.
  - **`lexemeText`**, `stepTexts`: each step read its kind's text
    (`IsWord`, `IsDigits`, `IsComment`, `StringRead`).
  - `assemble`'s fold: `addFine`, `foldFine` (the lexer's texts are an
    invariant of `Assembly.add`, each lexeme's slice of the source
    being what its step read), with `wordKindFine`, `symbolsKindFine`,
    `signKindFine`, `lexemeKindFine`, `withTrailingFine`.
  - **`lexTexts`**: `lex source = Ok lexed → FineTokens lexed.tokens ∧
    FineTrivia lexed.endTrivia`: every token's kind is `IsName`,
    `IsDigits` or `StringRead` where it has a text, and every comment
    above a token, after one, or at the end of the file `IsComment`.

**Program change:** `symbolsKind` matches the table's answer as a sign or
an operator and gives `Stray` otherwise, where it was `symbols run |>
.getOrElse (Stray run)`. The table gives only those, so it computes the
same (the 98 tests pass, 44 from the cache); the proof that a run of
operator characters is no name then doesn't read the table.

**Not checked against a broken program** this part: the new theorems are
about the lexer as it is, and no mutation was run.

**What is left of WF's token texts, and how.**

1. *Strings*: `StringRead text → IsString text`. `IsString` wants
   `Parse.ManyRuns stringSegment segments` (each piece read whole,
   before whatever follows), and `Reads` of `many` gives pieces without
   saying each plain run was the longest. Either merge neighbouring
   plain pieces (a flat predicate on the characters between the quotes,
   then the canonical pieces from it), or carry "the longest run"
   through `many` with `ReadsFrom`. About 10 lemmas.
2. *The parser copies them*: as part 7 planned, `value.texts ⊆` the read
   tokens' texts through `readsThen`, now with `FineTokens` as what the
   tokens satisfy. About 70 lemmas, then the tree induction (15).
3. *The last item's comma*: not looked at.

**Re-estimate** [estimated; this lane proved 68 theorems in about 20
minutes of the clock]: WF's token texts now 95 lemmas (strings 10,
parser 70, induction 15), a lane of its own; the other rows of part 7's
table are unchanged.

**Friction** (beyond parts 1 to 7):

42. **`Parse.Reads` can't say where a parse is.** Offsets are in
    `Parse.RunsFrom` (completeness) only, so soundness for anything that
    records offsets needed a second property (`Paced`) with a lemma per
    operation beside each `reads…` lemma. If `Reads` itself said the
    offset moved by `read.length`, `Paced` would not be needed; that
    changes every primitive's proof and no combinator's.
43. **`cases` splits the goal, never a hypothesis.** `lexemeStart
    [first, ..tail] = Some WordLexeme → isWordStart first = True` is
    open after `cases` whether the equation is a parameter or the left
    of an arrow. It took `charClass`, `guardedStart` and a `match` per
    test. With the equation in the goal as a Bool test it ran out of
    budget (24 splits).
44. **`pacedThen`/`readsThen` pick the wrong `p` and `j`** when the
    continuation ignores its argument (`let plain := Parse.span …; ()`)
    or the first step is `Parse.mark()`: the mismatch is reported on the
    first lemma. Giving `[p := …] [j := …]` fixes it, and a `match`
    can't be written in `[j := …]` (`E-MATCH-MOTIVE`), so
    `stringSegment` was done at the state level with `match e:`.
45. **`match e:` rewrites hypotheses after computing them**, which made
    the state-level proofs short, and makes arms unreachable that the
    checker then asks to have deleted (14 times here): pleasant.
46. **A one-line `match` in an arm takes the arms after it**
    (`| [char] => match p: … with | Some … | None … ` then `| [first,
    ..]`): the error is about a `List` pattern among `Option` ones.
47. **`True` in a `Prop`-valued `def` is proved by `rfl`, not
    `Trivial`** ("this test fact can't be built with `Trivial`").

### Part 9 (Fable, 15 Nov 2026): the parser copies the lexer's texts; `printedLexes` from `parse` alone

A 25-minute lane on the rest of WF's token texts. All three items of
part 8's list are proved, so "the printed text lexes to the file's
pieces" now has no hypothesis but `parse source = Ok file`
(`parsedPrintLexes`). Positions (`assemble` with `readingTracks`) are
not started, and there is still no `formatDirect`.

**Proved** (no open goals, no axioms; `audit Toy`: 801 theorems, 0
failed, the same 14 warnings as part 8; `audit Std.Parse`: 386
theorems, 0 failed, the 5 warnings of before):

- Std, `Parse/Among.sw` (18 theorems, new file; the prelude hash
  snapshot gains these names).
  - `Parse.ReadsAmong fine parser spec`: `Parse.Reads` with one more
    hypothesis on the run, that every item left is `fine`. What is left
    after a success is an end of what was left before, so the
    hypothesis carries through `then`. A parser's lemma may then use
    `fine` of any item it sees, read or only looked at.
  - `amongOf` (every `Reads` lemma is a `ReadsAmong` one), `amongDone`,
    `amongWeaken`, `amongThen`, `amongThenOf`, `amongOne` (the item
    `one` read is `fine`), `amongOptional`, `amongManyFrom`,
    `amongMany`, `amongMany1`, `amongRecursiveWithFuel`,
    `amongRecursiveWith`, `operatorsFromOkNext`, `amongOperatorsFrom`,
    `amongOperandsFrom`, **`amongOperators`** (as `readsOperators`, with
    `step` given that the operator's item is `fine`), `allHead`,
    **`wholeAmong`** (`whole items p = Ok value` on items all `fine`
    gives `spec items value`).
- `Fmt/ParsedProofs.sw` (72 theorems, new file). `Good token`: its
  kind's text is `IsName`, `IsDigits` or `IsString`, its comments
  `IsComment`. `Fair parser holds`: from tokens all `Good`, a success
  of `parser` gives a value that `holds`. One lemma per parser function,
  beside `ShapeProofs.sw`'s `gives…`: `fairSign`, `fairKeyword`,
  `fairName`, `fairSignInBrackets`, `fairItem`, `fairItemsFrom`,
  `fairItems`, `fairAtomOf`, `fairAtom`, `fairCallAfter`,
  `fairFieldAfter`, `fairSuffixes`, `fairPostfix`, `fairNegations`,
  `fairOperand`, `fairChain` (with `lexicalStep`: an operator's
  comments are its token's), `fairBare`, `fairInline`,
  `fairStatementLine`, `fairStatement`, `fairBlock`, `fairBodyFuel`,
  `fairBody`, `fairElse`, `fairExpressionRule`, **`fairExpression`**,
  `fairParameterStep`, `fairParameterList`, `fairParameters`,
  `fairFunctionLine`, `fairValueLine`, `fairDeclarationLine`,
  `fairDeclaration`, `fairFileEnd`, **`fairSourceFile`**; with
  `fineComments` (the comments the tree keeps of a good token are
  comments) and the list lemmas for notes, blocks and declarations.
  - **`parseLexical`**: `parse source = Ok file → LexicalFile file`.
  - **`parsedPrintLexes`**: `printedLexes` with `parse source = Ok file`
    in place of `LexicalFile file`.
- `Fmt/StringProofs.sw` (7 theorems, new file). **`stringReadClosed`**:
  `StringRead text.toList → IsString text`. The lexer's pieces are
  taken apart into characters and escapes (`eachPieces`), and those
  joined again into the runs `many stringSegment` reads before a
  closing quote, whatever follows it (`piecesRun`, with `plainFirst`
  for a plain character before each of the three ways the rest can
  start).
- `Syntax/ShapeProofs.sw`: `Shaped` now also says a list's last item and
  a call's last argument have no comma's comments (`BareLastItem`), so
  **`parseShaped`** gives it of every parsed tree (`givesItem`,
  `givesItemsFrom`, `givesItems`, `bareLastAppend`, `bareLastReverse`).
  Two read-back proofs and the example in `ExpressionProofs.sw` take
  the stronger `Shaped` apart.

**Program change:** `itemsFrom`'s out-of-fuel arm gives no items where
it gave the ones found (`found.reverse`). The arm is reached only with
no tokens left, so with nothing found: each round reads a token and
`fuel` starts as the tokens left. That is argued in a comment, not
proved; with it, "the last item has no comma's comments" needs no count
of tokens. Trees, goldens and messages are unchanged (the 98 tests
pass). The other way is a count through `Parse.Reads`' honest marks
(about 10 lemmas at the state level), keeping `found.reverse`.

**The plan changed: no `texts ⊆` form.** Parts 7 and 8 planned a flat
positive spec, `value.texts ⊆ taken.flatMap tokenTexts`, then a tree
induction. Two things rule it out: a token the parser only looks at
(`peek`, then `layout.comments token` in the tree) isn't in what a
`Reads` spec can speak of until it is read, and for a statement's notes
it is read by another parser altogether; and `Parse.readsOperators`
takes specs of the value only, while the operator's comments come from
its token. With "every item left is fine" as a hypothesis of the run
(`ReadsAmong`) the spec is of the value alone, `Lexical` itself, and
there is no tree induction: each `fair…` lemma is its `gives…` lemma
with the predicate changed and `among.left` where a token's texts go
into the tree.

**Checked against a broken program:** with `itemsFrom`'s arm put back
to `found.reverse`, `givesItemsFrom` fails. With `atomOf` giving `Var
"let"`, or `operatorOf` a made-up comment, the read-back proofs of
parts 2 and 3 (`ParserProofs.sw`, `operatorOfOp`) fail first, so the
check never reaches the `fair…` lemmas: not shown for them on their
own.

**What is left**, part 7's table with WF done:

| Layer | Left | Lemmas |
|---|---|---|
| A, engine | nothing | 0 |
| B, lexing | `assemble` over the steps | 15-20 |
| E, rules to tokens | positions (25), layer C read back (30), spelling the tree (40) | 95 |
| WF | nothing | 0 |
| D, parser | `if` with a block branch; the file from its spelling | 30-40 |
| Glue | `formatDirect`, round trip, idempotence | 10 |

Two lanes at this pace [estimated; this lane proved about 100 theorems in
about 25 minutes of the clock]: (1) positions, `assemble` and layer C's
read-back; (2) spelling the tree, the rest of D and the glue.

**Friction** (beyond parts 1 to 8):

48. **A `match` on a token's kind rewrites every hypothesis that
    mentions the token**, so `among: List.All Good state.at.rest`
    became `(IsName text ∧ …) ∧ List.All Good later` and no longer fits
    the lemma it has to be passed to (`E-TYPE-MISMATCH`, 26 times in
    one proof). Applying the lemma to everything but `h` in a `let`
    before the `match` fixed it. Friction 45's pleasant side has this
    cost.
49. **A `def` whose first arm takes a record apart is stuck on a
    variable**: `BareLastItem [first, next, ..]` didn't compute with
    the arm `[{ comma, .. }]`; `[last] => last.comma = …` does.
50. **A literal-character match is opened by its equation lemma, not
    by `match` on comparisons**: `segmentStart [char, ..rest]` stayed
    stuck after three `match … : char == '…'`; `segmentStart.eq2` with
    `char ∉ ['\\']` and the guard did it. Asking for the lemma's type
    with a wrong annotation (`let probe: Nat := segmentStart.eq2`) was
    the quickest way to see it.
51. **`rewrite <- equation in term` looks in the goal after computing
    it**, and a goal that is a `def` applied to a cons has computed
    away the cons; `rewrite equation at hypothesis` works there.
52. **Std's proofs can't be reused with one more hypothesis on the
    state**: `ReadsAmong`'s combinators are `Reads`' proofs again with
    `among` passed along (about 300 lines). If `Reads` took an
    invariant of the items left (any property kept by taking a start
    away), `Reads` would be the case `True` and friction 42's `Paced`
    might be another.
53. **The release binary reads std from the checkout**, so `task build`
    did nothing after a new std file and the checks saw it anyway;
    worth a line in the workflow notes.

### Part 10 (Fable, 15 Nov 2026): where the printed tokens are (layer B done), and the engine's half of positions

A 25-minute lane on positions. Layer B is finished: the tokens the
printed text lexes to are a function of the printed pieces alone, each
with its `startsLine` and `column` (`parsedPrintTokens`). The engine's
half of "where each word is" is proved too (`printLays`), with a probe
that the rules' documents meet it. The rules' half (that a file's layout
lays its words where the parser's layout rule wants them) is designed
below and not started, so nothing yet says a printed statement's first
token is at its block's column, and there is no `formatDirect`.

**Proved** (no open goals, no axioms; `audit Toy`: 891 theorems, 0 failed, 16 warnings: the 14 of part 9, and `putMid` and `putSpaces`, where the search finds no printer in the middle of a line; `midExample` is one):

- `Fmt/PlaceProofs.sw` (27 theorems, new file), layer B's last part.
  - `placed out`: the tokens of the pieces `out` (the last first), with
    no source: a piece of spaces is nothing, a line break puts a blank
    line waiting if its line was blank, a comment waits for the next
    token if alone on its line and goes on the newest token otherwise,
    and any other word is a token of the kind its text spells
    (`lexemeKind (lexemeOf piece) piece`), with `startsLine = lineBlank
    earlier` (only spaces before it on its line) and `column =
    lineWidth earlier` (part 5's width of the line so far, the printer's
    own column by `readingTracks`), `offset` the characters before it.
  - **`piecesTokens`**: for a source that is proper pieces joined,
    `assemble source (locatedSteps 0 (stepsOnto out []))` is `placed
    out`'s tokens and end trivia. On the way: `assembleLaid` (reading
    neighbouring pieces of spaces as one lexeme changes nothing:
    `gapFold`, `addPieceFold`, `ontoFold`), `addPlaced` (one piece:
    `Assembly.add` is `placePiece`, the line is then blank and as wide
    as `lineBlank` and `lineWidth` say), `laidPlaced` (the fold, with
    `lineStart + lineWidth out = charsLength out`), `charsOntoSplit`,
    `codeToken`.
  - **`joinedPlaced`**, **`printedTokens`**, **`parsedPrintTokens`**:
    `parse source = Ok file` gives, at every width, `(file.print
    width).text = pieces.joinWith ""`, `wordsOf pieces = wordsOf
    file.pieces` and `lex` of the text `= Ok` with `tokens = (placed
    pieces.reverse).tokens.reverse`, where `pieces` is `printedPieces
    file.layout width`, the pieces `print` joins, named so that other
    theorems speak of the same ones.
  - The token each class of word is placed as: `namePlaced` (`IsName
    text` gives a `Name text` token), `digitsPlaced`, `stringPlaced`,
    `keywordPlaced`, `signPlaced`, `operatorPlaced` (as `codePlaced`,
    the one shape of a code token), `ownLinePlaced`, `trailingPlaced`,
    `wordPlaced` (a piece that isn't layout goes through `placeWord`).
    `placedExample` computes three tokens' line starts and columns.
- `Doc/Places.sw` (62 theorems, new file), positions, engine half.
  - `eventsOf out`: the words of the output in order, each with `start =
    Some column` if only spaces come before it on its line, else `None`:
    exactly the `startsLine` and `column` `placed` gives a token.
  - `Lays doc indent place trace next`, in continuation style as
    `Joins`: from `place` (`AtStart indent`: nothing on the line, the
    next word starts it at that column; `Mid indent`: words on a line
    indented so; `Held indent`: also a trailing comment waiting) with
    `trace` printed, every way `doc` may print appends each word to the
    trace with where it starts its line, and hands every place it may
    leave to `next`. A word after a waiting comment starts a line at
    `max indent (line + 2)` (the comment break); `CommentEnd` goes back
    to the line's indentation; `OneLineBelow` is a line two deeper.
  - **`printLays`**: `Lays doc 0 (AtStart 0) [] spec` gives, at every
    width, `spec place (eventsOf (printedPieces doc width).reverse)` for
    some place: whatever the document says of its whole trace holds of
    the printed pieces. **`readingLays`** is the same of every reading
    with the steps to finish. On the way: `Agrees` (the printer is at a
    place and trace: line blank, indentation owed, line indent, the
    waiting comment already in the trace), one lemma per printer
    operation (`putStart`, `putMid`, `putSpaces`, `newlineAgrees`,
    `writeStays`, `sepSpace`, `lineStartStays`, `hereAgrees`,
    `blankStays`, `suffixStays`, `flushAgrees`), `stepLays` (26 arms),
    `laysWeaker` and the work-list lemmas, as in `Joins.sw`.
    `printLaysExample`: `f`, then `x` on its own line two in, has the
    trace `f` at `Some 0`, `x` at `Some 2`, at every width.
  - `Doc/Joins.sw`: **`printedJoins`**, `printJoins` of `printedPieces`.
- `Fmt/Tests/Places.sw` (4 tests): `reach`, `Lays` as a set of places
  without the trace, so that it runs. Every golden's and every comment
  probe's layout lays, whichever way groups, fills and choices go: the
  rules never reach a case `Lays` refuses.

**`Lays` refuses** (is `False` at) four things, none of which the rules
do on the goldens or probes: a chunk of spaces at a line start (the next
word would start its line one column on); a `Line` or fill separator at
a line start (a space there, or a blank line the tree doesn't have); a
trailing comment at a line start (it would lex as an own-line comment);
a second trailing comment while one waits (as `Joins`). Like `Joins` it
doesn't follow modes: a `Line` may be a space or a break anywhere.

**Checked against a broken program:** with `newline` owing one column
more than it was asked, `newlineAgrees` fails (with part 6's
`newlineSound`). No program changed in this part.

**What is left of E: the rules' half, as one induction.** With
`printLays` and `parsedPrintTokens` about the same pieces, spelling the
tree is a statement about `Lays file.layout 0 (AtStart 0) [] spec`:

1. Per rule, a lemma in `Lays`' own continuation style, as the `Joins`
   lemmas of part 7: for an expression in a statement at column `C`,
   printed in a construct indented `indent ≥ C` from a place whose line
   is indented at least `C`, `(∀ place events => Events C expr events →
   C ≤ place.indent → next place (trace ++ events)) → Lays expr.layout
   indent place trace next`. `Events` is the tree's words in order with
   what the parser's layout rule needs of each start: `None` or `Some
   deeper` for a token of the statement (`Layout.allows`), `Some C` also
   for `else`, anything inside brackets, the first token of each
   statement of a block at `Some B` for one `B > C`. This is layer C's
   scan (`LayoutProofs.sw`) said of positions; the scan itself isn't
   used. About 45 lemmas (one per rule, as `RuleJoinProofs.sw`).
2. A relation between `placed`'s tokens and events (same words, a code
   word's token has `startsLine` iff `start` is `Some`, and then that
   column; comments on the tokens the tree has them on), from
   `namePlaced` and the others, by induction over the pieces. About 15.
3. `Spelled`, `SpelledBody`, `SpelledLines` of the tokens from 1 and 2,
   then part 4's `runs…Spelled`. About 25. Blank lines (`blankBefore`
   against the `"\n"` pieces `Printer.blank` writes) aren't in the
   trace; they need `Blank` counted in `Lays` or a lemma of their own.

| Layer | Left | Lemmas |
|---|---|---|
| A, engine | nothing | 0 |
| B, lexing | nothing | 0 |
| E, rules to tokens | the rules' half of positions (45), tokens against events (15), spelling the tree with blank lines (25-35) | 85-95 |
| WF | nothing | 0 |
| D, parser | `if` with a block branch; the file from its spelling | 30-40 |
| Glue | `formatDirect`, round trip, idempotence | 10 |

Two lanes at this pace [estimated; this lane proved 90 theorems in
about 25 minutes of the clock]: (1) the rules' half and tokens against
events; (2) spelling, the rest of D and the glue.

**Friction** (beyond parts 1 to 9):

54. **A `match` with a `let`-bound proof as a second scrutinee is
    refused** (`E-MATCH-MOTIVE`, "the type of one scrutinee mentions
    another"), where the same proof as a theorem's parameter is
    accepted: `match waiting: printer.suffixes.isEmpty, known with`
    worked only after `known` became a parameter of a helper lemma
    (`writeStart`, `writeMid`, `writeHeld`).
55. **`rewrite` after an earlier rule finds terms only as the goal then
    computes**: after `widthPiece`, `(" ".repeat (Succ less)).length`
    had become `(List.replicate less [' ']).concat.length + … + 1` and
    `indentLength` no longer matched. Proving the equation apart with
    `omega` over `let`-bound facts, then rewriting once, worked.
56. **A `match name: condition` computes one side of an equation and
    not the other**: in `trimEvents` the goal became `if isLayout last …
    = if (decEq …).holds …`, which `rfl` refuses. A helper taking the
    Boolean and its equation as parameters (`trimEventsBy`) and
    rewriting with small equations (`trimKeep`, `trimDrop`) did it.
57. **`False` in a `Prop`-valued `def` is the Boolean** (`False =
    True`), so an impossible arm is `Void.exfalso (Bool.falseNotTrue
    never)`, not `Void.exfalso never`.
58. **A constructor is shadowed by a type of the same name in the
    importing namespace**: `Chunk` in `Toy.Fmt.Tests` is the disturber's
    type, so the pattern needed `Doc.Chunk`.

### Part 11 (Fable, 15 Nov 2026): the rules' half of positions, begun: tokens, closing brackets, rule triples

A 15-minute lane. The leaves of the rules' half are proved (a token and
a closing bracket with their comments, the breaks, the triples that put
rules one after another). The induction over the tree isn't started: it
is designed below, and it met a case that can't be proved of the rules
as they are (finding 1). Nothing yet says a printed file's tokens are
where the parser wants them; tokens against events, spelling and
`formatDirect` aren't started.

**Proved** (no open goals, no axioms; `audit Toy`: 927 theorems, 0
failed, the same 16 warnings as part 10), all in `Fmt/LaidProofs.sw`
(36 theorems, new file):

- `concatLays` (with `filterLays`, `emptyLays`): `Doc.concat docs` lays
  as the documents one after another (`LaysAll`).
- `wordLays`: a `Solid` text at any place is one event, `start =
  wordStart indent place` (`Some at` at a line start, `None` after
  words, `Some (max indent (at + 2))` after a waiting comment), and the
  line then has words on it.
- **`tokenLays`**: `token comments text`, with `Fine comments` and
  `Solid text`, from any place and trace, hands `next` exactly
  `tokenEnd indent place comments` and `trace ++ tokenEvents indent
  place comments text`: the comments above each at `breakColumn indent
  place` (where a `LineStart` there starts a line), the token (after
  them it starts their line; with none, where the place says), the
  trailing comment at `None`, left waiting. On the way `notesLay`,
  `aboveLays`, `trailingLays`.
- `Zone` (`Anywhere column`: in brackets in a statement at `column`;
  `Deeper column`: in the statement outside brackets), `Zone.allows`
  (`Layout.allows` of an event's start, for a token that isn't the
  statement's first), `Zone.holds` (an indentation no shallower than the
  statement), `Zone.under` (an indentation a line of the zone may start
  at), and of places `Inner` (a token that isn't the first may come),
  `Ended` (after a token), `Seated` (the line no shallower than the
  statement).
- `Rule within doc pre spec post`: in a construct whose indentation
  `within` holds of, from any place of `pre`, every way `doc` prints
  puts down events of `spec` and leaves a place of `post`. `RuleAll` of
  a list; `ruleNil`, `ruleCons` (the events are `Then first second`),
  `ruleLast`, `ruleConcat`, `ruleGroup`, `ruleNest` (inside a `Nest` of
  one or more, lines are deeper than the statement: `zone.under`),
  `ruleUnder`, `ruleWeaker`.
- **`tokenRule`**: `Rule zone.holds (token comments text) (Inner zone)
  (TokenAt zone.allows comments text) (Ended zone)`: a token that isn't
  its statement's first, wherever comments above it or a waiting comment
  start its line, starts only where the zone allows (`innerStart`,
  `innerLine`: a comment break is at `max indent (at + 2)`, deeper than
  the statement since its line isn't shallower).
- **`closerRule`**: `closer comments text` from any `Seated` place: the
  own-line comments at `indent + 2`, the bracket then at `Some indent`;
  `TokenAt anyStart`, since a closing bracket may start any line.
  `closerNotes` is its comment lines.
- `spaceRule`, `nothingRule`, `lineRule` (a `Line` in a nest: a space,
  or a line where the next token may start), `lineSeats` (a `Line` at
  the statement's own indentation: before `else` or a closing bracket),
  `softRule`, `hardRule`, `hardUnder`.
- `spacedTokens`: two tokens with a space between, by the triples
  alone: the shape of `let name` and of an operator and its operand.

No program changed.

**The induction, as designed (not proved).** `Events zone head expr
events`, a predicate by recursion on the tree as `Spelled`, in `Then`s:
`head` is asked of the leftmost token's start and `zone.allows` of the
others'; brackets' contents and items are `Events (Anywhere column)
anyStart`; a closing bracket is `TokenAt anyStart`; `else` is `TokenAt`
of "none, or at the statement's column or deeper". A body (a branch, or
after `=`) is either its one expression with `head := value.firstAbove
= [] → start = None` (inline: it doesn't start a line), or its lines at
one `column` with `zone.under column`, each statement `Events (Deeper
column) (start => start = Some column)`. The lemma per expression:

    Lexical expr → zone.holds indent → Seated zone place
      → head (wordStart indent (aboveEnd indent place expr.firstAbove))
      → (∀ after events => Events zone head expr events → Ended zone after → next after (trace ++ events))
      → Lays expr.layout indent place trace next

The leftmost token of every rule is printed at the rule's own
indentation, so its start is that function of the place
(`Expr.firstAbove`: the comments above the leftmost token). The pieces
are `tokenLays` for the head and the triples above for the rest (a
helper is wanted that runs a `RuleAll` after a lemma in this form).

**Findings.**

1. **A branch after a trailing comment on `then` or `else` can't be
   proved of `Lays`.** `branch` offers `Choice [" " value flat, below
   value]` whatever the keyword's comments. After `then -- note`, `Lays`
   (which doesn't follow `fits`) lets the first option print: the
   value's first token on a comment break at `max indent (at + 2)`,
   which the parser reads as a block at that column, and a later line of
   the value at `indent + 2`, which may be that same column: a new
   statement, `+ b`. Read from `Print.sw`, not proved: the engine
   doesn't do it in a broken group (`fitsFrom` refuses a chunk after a
   waiting comment, so `choose` takes `below`), and a group around a
   waiting comment and a chunk isn't flat for the same reason. Either
   way it is a fact about `fits`, which the proof has kept out of. `afterEquals`
   says it in the rule (`if equals.after.isNone`); `branch` should too:
   `branch keyword body`, inline only if `keyword.after.isNone`. The
   output is unchanged if the argument above is right (goldens to
   confirm). It touches `branchKeeps`, `branchPasses`, `branchWrites`
   and the three `if` lemmas that take them. Not done here.
2. **An inline body's first token has no comments above** in a parsed
   tree (above a token that starts a line deeper they are the block's
   notes), and the rules lean on `fits` for it too (`Flatten` refuses
   `LineStart`). `Events` above states the inline case under
   `value.firstAbove = []`, so the rules' half needs no hypothesis; step
   3 needs the fact from the parser, a new WF item (about 15 lemmas in
   `ParsedProofs.sw`'s style), or the same guard in the rules.
3. **Inside brackets the statement's column still matters**: the zone
   there is `Anywhere column`, not a zone without one, since the closing
   bracket's line must be shown no shallower than the statement for the
   tokens after it.

**What is left**, part 10's table with this part's work taken off:

| Layer | Left | Lemmas |
|---|---|---|
| E, rules to tokens | `branch` by its keyword (finding 1; 10); `Events` and the induction (35-40, the leaves done); tokens against events (15); spelling the tree with blank lines (25-35) | 85-100 |
| D, parser | `if` with a block branch; the file from its spelling; an inline body's first token has no comments above (finding 2; 15) | 45-55 |
| Glue | `formatDirect`, round trip, idempotence | 10 |

Two to three lanes at this pace [estimated; this lane proved 36
theorems in about 15 minutes of the clock, and stopped for context,
not time]: (1) `branch`, `Events` and the induction; (2) tokens against
events and spelling; (3) the rest of D and the glue.

**Friction** (beyond parts 1 to 10):

59. **A constructor named as an existing `def` of the namespace makes
    every use of that name ambiguous, in other files too**: `type Zone =
    | Loose | …` broke `JoinProofs.sw`'s `Loose` (`E-AMBIGUOUS` at each
    use, none in the new file). The zones are `Anywhere` and `Deeper`.
60. **`_` for a continuation argument isn't worked out** from the
    expected type (`wordLays … _ …`: "wasn't worked out from the other
    arguments"); each continuation is written out, which is most of
    `closerRule`'s length.
61. `omega` knows `Nat.max` (`innerStart`, `innerLine`), which the
    notes didn't say.

### Part 12 (Fable, 15 Nov 2026): the rules' half of positions, done: `Events`, the induction, `printedEvents`

A 25-minute lane. The rules' half of positions is proved for the whole
tree: at every width, the words of a parsed file's printed pieces, each
with where it starts its line, are the file's `FileEvents`
(`parsedPrintEvents`). Tokens against events, spelling and
`formatDirect` aren't started; the design for the first is below, and
it needs blank lines counted in the engine's half first.

**The program changed** (part 11's finding 1, the orchestrator's
decision): `branch keyword body` offers the inline option only when
`keyword.after.isNone`, and a one-expression branch after a trailing
comment on `then` or `else` goes below, as `afterEquals` does for `=`.
The output is unchanged: all 102 tests pass (goldens, probes, the
disturber). `branchKeeps`, `branchPasses`, `branchWrites` take the
keyword's comments; the `if` and `else` lemmas pass them.

**Proved** (no open goals, no axioms; `audit Toy`: 1016 theorems, 0
failed, the same 16 warnings as part 11), all in `Fmt/EventProofs.sw`
(89 theorems, new file):

- `Events zone head expr events`, by recursion on the tree in `Then`s:
  the expression's tokens in order as `TokenAt`s, the leftmost starting
  as `head` says, every other where `zone.allows`; inside brackets
  `Events zone.inside anyStart` and `ItemEvents` (`zone.inside` is
  `Anywhere` at the statement's column); a closing bracket `TokenAt
  anyStart`; `else` `TokenAt zone.reaches` (not at a line start, or no
  shallower than the statement). `BodyEvents zone body`: the body's one
  expression on its keyword's line (`InlineEvents`: `Events zone
  (inlineHead zone value)`, where `inlineHead` says the first token
  starts where the zone allows, and not at a line start if it has no
  comments above), or `∃ column`, `zone.under column`, with `LineEvents
  column`: each statement's first token `atColumn column`, the rest
  `Events (Deeper column)`; a comment line is one event at the column.
  `DeclarationEvents` (column 0; a function is `fn name (` as one
  group, `ParameterEvents`, then `) =` and the body), `FileEvents`.
- `HeadRule zone doc above spec`: as `Rule`, for a document whose
  leftmost token is printed at the construct's own indentation: from any
  `Seated` place, whatever `head` holds of where that token starts
  (`wordStart indent (aboveEnd indent place above)`), `spec head` holds
  of the events. `tokenHead`, `headCons` (a `HeadRule` then a
  `RuleAll`), `headInner` (not the statement's first: `zone.allows`, by
  `innerStart`), `headInside` (inside brackets: `anyStart`).
- **`exprLays`**: `Lexical expr` gives `HeadRule zone expr.layout
  expr.firstAbove (head => Events zone head expr)`, for every zone. One
  arm per construct; with it, mutually, `chainLays` (P6: a chain's parts
  from its left-nested tree, as `chainPasses`), `sepsItems` and
  `fillItems` (items as a fill lays them; `joinedFill` turns a fill
  into the `Line`-joined list of a call's arguments), `branchLays`,
  `elseBranchLays`, `afterEqualsLays` (each a `BodyRule`: from right
  after the keyword, with its trailing comment waiting or not,
  `trailEnd line keyword.after`), `blockLays`, **`linesLay`** and
  **`statementLays`** (a block's lines at `column`).
- The pieces: `linkRule` (P6), `closeAfterRule`, `nestFill` (P5),
  `nestJoined` (P4, P2), `softCloser`, `emptyCloser`, `itemRule`,
  `keyCons` and `keyLast` (a keyword, its body, what follows),
  `inlineLays`, `belowCore`, `belowValue`, `bareAfterEquals` (P3's
  three choices), `elseBare` (`else if` on one line), `bindingRule`
  (`let`, a statement or a declaration), `lineStartLays`; the silent
  ones without a `Done` in the events (`spaceAll`, `gapAll`, `lineAll`,
  `lineSeatsAll`, `sepSeats`, `softSeats`); `seatedHead`, `seatedReach`,
  `inlineStart`, `startAt`, `endedUp`.
- Declarations and the file: `fillParameters`, `openingRule`,
  `closingLays`, `functionLays` (P2), `declarationLays`,
  `declarationsLay` (P9), **`fileLays`** (`LexicalFile file` gives
  `Lays file.layout 0 (AtStart 0) [] next` whenever `next` takes every
  trace of `FileEvents file`).
- **`printedEvents`**, **`parsedPrintEvents`**: `parse source = Ok
  file` gives, at every width, `FileEvents file (eventsOf (printedPieces
  file.layout width).reverse)`: the pieces `parsedPrintTokens` lexes.

**What the statement doesn't say yet.** `FileEvents` is about words
and line starts, not tokens: nothing here says the lexer's tokens of
the printed text have these `startsLine` and `column` (that is tokens
against events), and kept blank lines aren't in the events.

**Tokens against events, as designed (not proved).** `placed out` reads
the `"\n"` pieces for `BlankLine` trivia and `eventsOf out` drops them,
so the tokens aren't a function of the events as they are. Two steps:

1. Count blank lines in the engine's half: `eventsOf` gives an event
   for a `"\n"` on a blank line (exactly when `placePiece` adds a
   `BlankLine`), `Lays` appends it at `Blank`, and refuses a line break
   at a line start anywhere else. `stepLays`' arms for `Blank` and the
   breaks change (`Doc/Places.sw`); `lineStartLays` here then says where
   the rules put blank lines (`blankBefore`, P9). About 10 lemmas.
2. `placed out` from `eventsOf out` alone, by induction over the pieces
   (`wordPlaced`, `namePlaced` and the others, `ownLinePlaced`,
   `trailingPlaced`): a code word is a token with `startsLine` iff
   `start` is `Some`, and then that column; a comment at a line start
   waits for the next token, another goes on the newest; offsets only
   grow. About 15.

**Findings.**

1. **Three parser facts the spelling step needs** (WF items, in
   `ParsedProofs.sw`'s style; none proved): (a) part 11's finding 2, an
   inline body's first token has no comments above (`inlineHead` is
   stated under `value.firstAbove = []`); (b) the same of every
   statement's and declaration's first token (the tree's rule that
   those comments are note lines; printed with them, the lexer gives
   them to the token and the parser makes notes of them, a different
   tree); (c) inside brackets a body is one expression (`blockAhead
   InBrackets` is `False`), so a block there never comes from the
   parser, though `BodyEvents` describes what the rules would print.
2. **Inside brackets `BodyEvents` is stronger than the parser needs**:
   a branch printed below is `LineEvents column` with `Deeper column`
   starts, where the parser asks nothing of starts. Spelling needs
   `Events (Deeper column) head` weakened to `Events (Anywhere column)
   anyStart` (monotone in the zone and the head: about 8 lemmas).
3. **`DeclarationEvents` of a function nests `fn name (` as one
   `Then`**, as the header's document does. Reassociating is
   `thenAssoc`.

**What is left**, part 11's table with this part's work taken off:

| Layer | Left | Lemmas |
|---|---|---|
| A, engine | blank lines counted in `Lays` and `eventsOf` | 10 |
| E, rules to tokens | tokens against events (15); `Events` weaker in the zone (8); spelling the tree with blank lines (25-35) | 50-60 |
| D, parser | `if` with a block branch; the file from its spelling; the three first-token and bracket facts (finding 1; 20) | 50-60 |
| Glue | `formatDirect`, round trip, idempotence | 10 |

Two lanes at this pace [estimated; this lane proved 89 theorems in
about 22 minutes of the clock, and stopped for context, not time]: (1)
blank lines and tokens against events, then the WF facts; (2) spelling,
the rest of D and the glue.

**Friction** (beyond parts 1 to 11):

62. **A `def` by arms needs a pattern for every argument after the
    colon** (`E-ARITY`), so a predicate that returns a function is
    `def Events (zone …) (expr: Expr): List Event → Prop := match expr
    with …`. Recursive calls left partly applied (`Then (Events zone
    head left) …`) pass the termination check, and compare without eta.
63. **A mutual call with an argument rebuilt from the caller's pattern
    isn't smaller** (`joinedFill [second, ..more]` from `joinedSeps
    second more`): the step lemma takes the recursive fact as a
    hypothesis (`joinedStep`), as `ifPasses` does.
64. **`rewrite <- found in lays` finds nothing once the goal has
    computed past the term** (`ChainLays [first, ..links] …` is already
    its `Lays`): a cast lemma over a variable does it (`chainCast`).
65. Good: an arm whose hypothesis computes to `False = True` is
    reported unreachable (`W-UNREACHABLE`) and can be left out
    (`chainParts … ++ [link]` as `[]`).
66. `W-ARROW-FORALL` is reported for every binder of every theorem in
    the `theorem name ∀ (x: T) (h: P): Q` form, several lines each, so
    `grep -v` doesn't filter it; errors were read with an `awk` filter
    on `[E-` blocks.

### Part 13 (Fable, 15 Nov 2026): blank lines in the trace, tokens from events, events inside brackets, std's leftmost-operand lemma

A 27-minute lane. Blank lines are counted in the engine's and the rules'
halves, and tokens against events is done: for every parsed file at
every width, the printed text lexes to tokens whose kinds, comments,
line starts (with their columns) and blank lines are read off a trace
that is the file's `FileEvents` (`parsedPrintViews`). `Events` is
weakened for brackets. Of the three parser facts none is proved: two
need "the expression's leftmost token is the first token read", which
no value-only invariant says; the std lemma for it is proved
(`Parse.readsOperatorsLeft`), the walk through the toy's parser isn't
started. Spelling isn't started.

**No program changed.** The probe `Fmt/Tests/Places.sw` (`reach`)
follows the new `Lays`, with one more test; all 103 tests pass.

**Proved** (no open goals, no axioms; `audit Toy`: 1048 theorems, 0
failed, the same 16 warnings; `audit:touched -- Std.Parse`: 389
theorems, 0 failed, 5 warnings, none of them new):

- `Doc/Places.sw`, blank lines in the engine's half.
  - `eventsOf` gives `Event.blankLine` (the event whose word is
    `"\n"`, which no word is) for a line break on a line with nothing
    but spaces: exactly when `placePiece` adds a `BlankLine`.
    `eventsGap`, `eventsBreak`, `eventsBlank`.
  - `Place` has a fourth place, `Broken indent`: a line start right
    after the line break that ended a line of words. `Lays` at `Blank`
    appends the blank-line event there and goes on at `AtStart`; at
    `AtStart` it refuses a `Blank` (the printer may or may not leave a
    line there: it reads its own count of line breaks); after words a
    `Blank` is nothing. A `HardLine` needs words on the line
    (`place.midLine`) and hands the document the choice of `Broken`
    or `AtStart`; `CommentEnd`, `OneLineBelow` and `SoftLine` need
    words on the line too: at a line start each would leave a blank
    line the tree doesn't have.
  - `Agrees` holds the printer's `newlinesAtEnd` (0 after words, 1 at
    `Broken`) and `started`. `newlineBroken`, `brokenStart`,
    `blankAdds`, `blankSame`, `blankStays`, `writeBroken`, `sepMid`,
    `softMid`, `startMid`; `stepLays` and `printLays` as before, of the
    new `Lays`.
- `Fmt/LaidProofs.sw`, `Fmt/EventProofs.sw`, the rules' half with blank
  lines. `LineEvents` is the first statement then `LaterLines`, each
  later line after `blankEvents blankBefore` (`[Event.blankLine]` or
  nothing); `DeclarationsEvents` and `LaterDeclarations` likewise, so
  `FileEvents` holds the file's kept blank lines. `laterStart`
  (`lineStart (index + 1)` after a line of words), `linesLay` and
  `laterLay`, `declarationsLay` and `laterDeclarationsLay`, `endedMid`,
  `trailMid`. `softSeats`, `softRule`, `hardRule`, `hardUnder` are
  stated after a token (`Ended`); `belowValue` and `blockLays` take
  `place.midLine = True`. `fileLays`, `printedEvents` and
  **`parsedPrintEvents`** read as before, of the new `FileEvents`.
- `Fmt/TokenEventProofs.sw` (9 theorems, new file), tokens against
  events.
  - `TokenView`: a token without its offsets: `kind`, `start` (its
    column if it starts its line, else `None`), `above`, `trailing`
    (the comment, without where it is). `viewOf`, `Placed.views`.
  - `viewsOf events`: the views a trace lexes to, an event at a time
    (`viewEvent`): the blank-line event waits (`addBlank`); a comment
    that starts its line waits, another goes on the newest token; any
    other word is a token of the kind its text spells, starting as the
    event says.
  - **`placedViews`**: `(placed out).views = viewsOf (eventsOf out)`,
    for every list of pieces. `pieceViews`, `breakViews`, `wordViews`,
    `gapPlaced`, `trailingViews`, `viewsSnoc`. `viewsExample` computes
    two tokens, a blank line and a trailing comment.
  - **`parsedPrintViews`**: `parse source = Ok file` gives, at every
    width, events with `FileEvents file events`, and tokens and end
    trivia (stated the newest first) with `lex (file.print width).text
    = Ok { lexemes, tokens = tokens.reverse, endTrivia =
    endTrivia.reverse }`, `tokens.map viewOf = (viewsOf events).views`
    and `endTrivia = (viewsOf events).pending`.
- `Fmt/BracketEventProofs.sw` (8 theorems, new file), part 12's finding
  2. **`eventsFree`**: `Events zone head expr events` and `head ⊆ wide`
  give `Events (Anywhere 0) wide expr events`, for every zone
  (`Anywhere 0` allows every start, and `else` anywhere). `itemsFree`,
  `bodyEventsFree`; **`bodyFree`**: a body of one expression, laid on
  its keyword's line or below it, is `Events (Anywhere 0) anyStart` of
  the expression: what the parser reads inside brackets. `tokenWider`,
  `thenWider`.
- Std, `Parse/ReadsOperators.sw` (3 theorems).
  **`Parse.readsOperatorsLeft`**: what `Parse.operators` read starts
  with what its first operand read (`taken = firstRead ++ more`, `first
  firstRead start`), and `kept start value` for any `kept` that holds
  of a value and itself and that joining a right side keeps.
  `readsOperandsFromLeft`, `readsOperatorsFromLeft`. The prelude's hash
  snapshot has the six new entries and no other change.

**What the statements don't say yet.** `TokenView` has no offsets, and
the parser asks two things of them: whether a token is its statement's
first (`Layout.allows`, `Layout.comments`: `token.offset == start`).
Spelling needs the printed tokens' offsets to be distinct (they grow:
`placed` gives each `charsLength earlier`); part 12's plan had that in
this step and it isn't proved (about 5 lemmas in `PlaceProofs.sw`). A
token's column is in its view only when it starts its line; the parser
reads it only then (read from `Parser.sw`: every use is beside
`startsLine`).

**Findings.**

1. **Parser facts (a) and (b) are not value-only.** That a statement's
   expression has no comments above its first token holds because that
   token is the statement's first (`Layout.comments` drops them at
   `offset == start`), so the proof must say the tree's leftmost token
   is the first token read. `Gives` (part 4) ignores what was read, and
   `Parse.readsOperators` is an invariant of values alone. `Parse.Reads`
   does give the tokens read, so the walk is possible: a spec `Heads
   layout taken value` (`taken = [token, ..rest]`, `value.firstAbove =
   (layout.comments token).above`) through `atomOf`, `atom`, the
   suffixes, the negations, `operators` (by `readsOperatorsLeft`, `kept`
   = same `firstAbove`), `expressionRule` and `readsRecursiveWith`; then
   a tree-wide predicate over statements, blocks, bodies, declarations
   and the file, as `ShapeProofs.sw` does for `Shaped`. Fact (c) (a
   body inside brackets is one expression) is value-only given the
   layout and can ride in the same walk. About 60-70 lemmas [estimated
   from `ShapeProofs.sw`'s 67], a lane of its own.
2. **Two ways to make (b) cheaper, both decisions.** (i) The parser
   could drop the comments above a statement's first token from the
   tree it built (a `withoutFirstAbove` on the statement) instead of by
   offset in `Layout.comments`; (b) is then an induction on the tree
   (10 arms), but `BlockProofs.sw`'s read-back changes with it, and the
   same output rests on the leftmost-token fact until that is proved.
   (ii) `formatDirect` could check the fact on the tree at run time, a
   walk and not a re-parse. Neither is done.
3. **Fact (a) is false inside brackets** (read from `Parser.sw`, not
   run): `(if a then` / `-- c` / `b else c)` reads `b` as an inline
   body with `c` above it, since inside brackets no body is a block.
   `inlineHead` already allows it (it asks `start = None` only when
   nothing is above), and spelling there goes by `bodyFree`. Outside
   brackets (a) needs a lexer fact as well: a token that doesn't start
   its line has nothing above it (about 5 lemmas, as `addBlankFine`).
4. `softRule`, `hardRule` and `hardUnder` (`LaidProofs.sw`) are used by
   nothing; they could go.

**What is left**, part 12's table with this part's work taken off:

| Layer | Left | Lemmas |
|---|---|---|
| A, engine | nothing | 0 |
| E, rules to tokens | the printed tokens' offsets grow (5); spelling the tree from `viewsOf` and `FileEvents` (25-35) | 30-40 |
| D, parser | the first-token and bracket facts (finding 1; 60-70, or less by finding 2); `if` with a block branch; the file from its spelling (30-40) | 90-110 |
| Glue | `formatDirect`, round trip, idempotence | 10 |

Three lanes at this pace [estimated; this lane proved 40 theorems and
restated about 25 in 27 minutes of the clock]: (1) the parser-facts
walk; (2) offsets and spelling; (3) the rest of D and the glue. The
parser layer is larger than part 12 thought (20 lemmas for the three
facts), because of finding 1.

**Friction** (beyond parts 1 to 12):

67. Good: a new constructor of `Place` went through four proof files in
    three check runs. Every `match` that needed an arm was listed
    (`E-NONEXHAUSTIVE`), and arms whose hypothesis computes to `False`
    (`Seated zone (Broken at)`) needed none.
68. Good: equations chained with `Eq.trans` and `Eq.cong` over named
    terms checked first time where parts 10 to 12 fought `rewrite` over
    terms the goal had computed past (frictions 55, 56, 64): conversion
    does the unfolding (`pieceViews`, `breakViews`).
69. **A number in a pattern needs a catch-all arm even when an equation
    scrutinee rules the others out** (`match count: n, one with | 1, _
    =>`, `E-NONEXHAUSTIVE`): `rewrite one in rfl` instead (`blankAdds`).
70. **A std lemma costs a lane about four minutes of tests** for three
    theorems: `audit:touched` 27 s, `the_library_has_no_unreachable_arms`
    95 s, `hash_stability` 112 s, and the prelude snapshot is accepted
    by hand (the `.snap.new`'s header differs by a line).
71. `W-ARROW-FORALL` no longer floods (SW-3439): a check with one type
    error and no parse error printed that error and nothing else.

## Every comment placed (SW-3450, D3618, D3619)

Every token now holds its comments in the tree (`Comments = { above,
after }` on each name, literal, keyword, sign and operator; an item's and
a parameter's comma carry their own), and `AsWritten` is gone: the
parser never decides anything from comments, and the rules print each
token's comments beside it. The one exception is the own-line comments
above a statement's or declaration's first token, which stay note lines
(`Layout.comments` leaves `above` out for that token), so blocks read as
before.

**The engine's comment break.** Text after a waiting trailing comment
starts a new line at `max indent (lineIndent + 2)`, so code after a
comment is at least two deeper than the comment's line; all-space text
there is dropped. Own-line comments inside an expression are
`LineStart` (a break unless at a line start), the text, `CommentEnd` (a
new line at the comment line's indent). A closer with comments above it
uses `LineStartHere` so the comments sit one level in and the closer
back at the bracket's line. `fits` is conservative: any chunk after a
waiting comment doesn't fit, so a group holding a trailing comment
breaks. SW-3447's printer measures from the new line instead; that would
need `fits` to know the indent and width, a change to the budget proofs.
The cost is layouts like `fn f(\n    x\n) -- c\n  = x` (a header with a
comment after `)` breaks its parameter list): odd but stable.

**Goldens.** The 20 Sprig probes of the proposal are goldens
(`Fmt/Tests/Probes.sw`): each parses to its dump, formats to its text,
formats again unchanged, and survives 50 disturbances. Of the existing
goldens, only `comments` changed, and only where forced: its
`fn odd(x) = -- why` declaration was kept as written (`x  %  2`) and is
now formatted (`x % 2`); the `-- loyal` comment now hangs on the call's
`)`, the token it follows.

**Proofs.** Everything checks and `audit Toy` is clean (233 theorems,
0 failed; the 9 warnings are the audit finding no input for
hypotheses about parser states or a text that opens a line, as before).

- Restated against the new tree (comment slots): `runsSign`, `runsName`,
  `runsKeyword`, `runsElse` (they give the token's comments);
  `runsAtomName`/`Number`/`String`/`Bracketed`/`List`, `runsNegation`,
  `runsSuffixesField`, `runsSuffixesCall`, `operatorAt`,
  `operatorFound`, `runsIf`, `runsIfSpelled` (each constructor's comment
  fields from `Layout.comments`); `Spelled`, `SpelledInline`,
  `SpelledItems`, `SpelledLines` (each adds the equalities of the
  comment fields); `runsItemLast`, `runsItemComma`, `runsItemsFrom`,
  `itemsStart`, `runsItems` (the comma's and the closer's comments);
  `runsBareStatement`, `runsInlineBody`, `runsBodyInline`, `bodyOf`
  (no `trailingFor`, no start mark); `runsLineLet`, `runsLineOther`,
  `runsLineBare`, `runsStatement` (the first token instead of a mark);
  `runsDeclaration`, `runsDeclarationValue`, `runsDeclarationFunction`,
  `runsValueSpelled`, `runsFunctionSpelled`, `runsSourceFile`,
  `parseReads`, `declarationStops`, `declarationDeclines` (no source
  text: nothing is cut from it); the parameters (`ParameterSteps`,
  `parameterRounds`, `runsParameters`, `runsNoParameters`, now over
  `Parse.optional parameterList`, which keeps each comma's comments).
- Gone with what they were about: `lastComment`, `runsLastTrailing`,
  `trailingFor`, `runsTrailingSince`, and `CommentProofs.sw` (the rules'
  suffix lemmas: the engine now breaks after a comment itself, proved in
  `Doc/Proofs.sw` as `textAfterComment`, `spacesAfterComment`,
  `continuationDeeper`).
- Layer C (`LayoutProofs.sw`): the scan's state is `Scan = Clear |
  Waiting | Started (opens: Bool)`, so a line that ends in `CommentEnd`
  counts as an own-line comment whatever its text; `statementScan` and
  `declarationScan` now say the scan ends settled, and
  `declarationScan` lost its `AsWritten` hypothesis. The per-construct
  lemmas became `…Keeps` (from a settled scan, the document leaves it
  settled).
- `formatFile*` in `Fmt/Proofs.sw` lost `printed.asWritten` (forced).
- The non-comment lemmas keep their statements.

### Part 14 (Fable, 15 Nov 2026): the rest, top-down (D3620)

No proof in this part. `sketch/src/Sketch.sw` (a project of its own,
`check: open-goals: warn`) defines `formatDirect` and proves
`printParses`, the round trip, idempotence and `formatAgrees` from five
open lemmas and what is proved here, so the remaining path is those
five statements and two definitions that must widen. [SKETCH.md](SKETCH.md)
has the table (200-250 lemmas, 5-6 lanes planned), two new findings (no
body keeps a blank line above its first line; a `then` or `else` may
stand at the column of the block before it) and the recommendation.

### Part 15 (Fable, 15 Nov 2026): expressions are spelled (D3621, lane 1 of 6)

A 25-minute lane. Goal E2 is proved for expressions:
`Fmt/SpellProofs.sw` (56 theorems, new file; `audit Toy`: 1104
theorems, 0 failed, the same 16 warnings). No program changed.

- **`exprSpells`**: the events of an expression, seen after whatever
  trivia waits, are views (`Seen`), and tokens with those views spell
  the expression (`Spelled`) at the layout, wherever its statement
  starts: every form inside brackets, every form but `if` outside them
  (`Covered`). With it `itemsSpell`, `bodySpells` (a branch inside
  brackets), `inlineSpells` (a body on its keyword's line, any layout),
  `bareSpells` (a statement that is an expression, from its line start:
  the first token is the layout's start, the rest have rising offsets),
  `spellsBracketed` (from `viewsOf`, the newest first).
- `HeadedFile` and its family moved from the sketch into this file
  (`Headed` is `HeadedExpr`: `StringProofs.sw` has a `Headed`).
- The sketch still has five open goals; E2's comment says what is no
  longer part of it. [SKETCH.md](SKETCH.md), "After lane 1", has the
  count against the estimate (56 against 45-50), what was found, and
  the new estimate (180-220 lemmas left).

**Not done:** `if` outside brackets (statement change 1, which is
larger than part 14 said: a block's end is a fact about the tokens
after it, and `Spelled` has none); `EndsExpression`; blocks, lines,
declarations.

**Friction** (beyond parts 1 to 14):

72. Good: 1,400 lines of proof terms checked with four small errors,
    none in the ten-arm induction. Taking a list apart by continuation
    (`viewsCons goal tokens … (first rest … => …)`) needed no `rewrite`
    and no casts of hypotheses.
73. A `match` inside a lambda passed as an argument has "no definition
    to lift it into" (`E-MATCH-MOTIVE`); `h.left` did it.
74. `match h: a == a, sameOffset a with` is refused (one scrutinee's
    type mentions another); a helper with the equation as a parameter
    does it (`firstComments`).
75. A new `def` named like a constructor elsewhere in the namespace
    (`Plain`) breaks the patterns that use the constructor, with an
    error at each of them and none at the `def`.

### Part 16 (Fable, 15 Nov 2026): blocks in an `if` read back (D3, D4, statement change 1; lane 2 of 6)

A 25-minute lane. Two of the sketch's goals are discharged and the
statement that was too narrow is widened: `audit Toy`: 1131 theorems,
0 failed, 18 warnings (the 16, and `fuelDeclines` and
`expressionDeclines`, whose hypothesis "this token is a keyword" no
random token met). No program changed. The sketch has four open goals.

- **D4**: a block ends where no token starts a line at its column, or
  at `then` or `else` wherever it stands (`BlockEnds`).
  `statementDeclinesEnd`: `statement` declines there, because no
  expression starts with a keyword other than `if`
  (`expressionRuleDeclines`, for any nested parser).
- **D3**: `linesRun` and `runsBodySpelled` are over the parser of the
  induction (`ReadsNested`, `DeclinesNested`); `runsBodyNested` is
  proved and `runsBody` is its instance at `expression`.
- **Statement change 1**: `Spelled`'s arm for `If` asks `SpelledBody`
  of each branch before whatever may follow it (`After`:
  `EndsExpression` and `Settled`). `runsIfSpelled` reads the branches
  by `runsBodyNested`. `runsExpression` is an induction on the fuel of
  its own (`runsExpressionFuel`).
- **`afterDeeper`** (E2's): what may follow a statement may follow the
  last line of a block inside it, and ends the block.
- **`runsIfBlockExample`**: `if a then`, the block `b`, `else c` with
  `else` at the block's column, by `runsExpression`.

[SKETCH.md](SKETCH.md), "After lane 2", has the statement as made, the
counts (28 new theorems against 38-57) and the new estimate (140-165
left).

**Not done:** `if` outside brackets in E2: it is the same induction as
E2's blocks (a branch is a body, a block's line is an expression), not
a step before it.

**Friction** (beyond parts 1 to 15):

76. One unbalanced bracket in a 1,600-line file gave 2,242
    `W-ARROW-FORALL` warnings (every binder of every theorem after it
    read as a function type) and unknown-name errors in five other
    files; the `E-PARSE` was at line 1,261 of 14,000 lines of output.
77. `rfl` can't run a parser through `Parse.note` (the state's `note`
    branches on offsets it doesn't know), so "declines" is built from
    `Parse.declinesAfter` and `declinesBind`; each `match` on the next
    token needs its own step lemma under `optional`, by taking the
    state apart (`chainRuleStops`). `rewrite starts in rfl` on such a
    step failed where the two sides unfold to different depths.
78. Good: `Spelled` (one file) and `SpelledBody`, `SpelledLines`
    (another file of the namespace) became mutual without moving. The
    termination check wanted the body's one expression matched as a
    part of the body, not `∃ value` with an equation, and said so.
79. Good: the whole statement change (two definitions, six restated
    theorems, three files) checked after two bracket-count errors and
    nothing else.
80. std has no way to tell `Parse.runsRecursiveWith`'s step anything
    about the nested parser except what it reads; "it declines here"
    needed the fuel induction copied (`runsExpressionFuel`).

### Part 17 (Fable, 15 Nov 2026): the parser clears first-token comments; D1, E1 and D2 (lane 3 of 6)

A 20-minute lane. Three of the sketch's four goals are discharged:
`audit Toy`: 1210 theorems, 0 failed, 18 warnings (as before). The
sketch has one open goal, E2 (`spellsFile`). One program change, the one
decided for D1: `bareStatement` clears the comments above its
expression's first token outside brackets (`Layout.headed`). Goldens,
probes and messages are unchanged (103 tests, run without the cache).

- **D1** (`parseHeaded`, `Fmt/HeadProofs.sw`): every parsed file is
  `HeadedFile`. `ShapeProofs.sw`'s walk again, with `HeadedExpr
  (bracketedOf layout)` for `Shaped`. Facts (a) and (b) come from the
  clearing (`headedBare`) and, for `let` and `fn`, from
  `Layout.comments` at the statement's own start (`startAbove`); (c)
  from `bodyFuel` inside brackets reading `inlineBody`; (d) from
  `withoutFirstBlank` (`unspacedWithout`).
- **The read-back keeps up**: `runsBareStatement` takes
  `layout.headed value = value`. `SpelledOne` and `SpelledInline` ask
  it; a statement's own expression has it from its spelling
  (`spelledFirstAbove`: the comments above a spelled expression are its
  first token's; `spelledHeaded`). `Shaped` and `Lexical` survive
  clearing (`shapedCleared`, `lexicalCleared`).
- **E1** (`placedOffsets`, `Fmt/PlaceProofs.sw`): each new token is at
  the length of the text before it, and a piece that isn't spaces has a
  character, so the newest token's offset is below the text's length and
  above the one before (`placedBelow`).
- **D2** (`runsFileSpelled`, `Syntax/FileProofs.sw`): `declarationsRun`
  is `linesRun` for the file's repetition; no fuel or bound, since
  `runsValueSpelled` and `runsFunctionSpelled` read each declaration
  whole.

Counts against the estimates, the new obligation (`layout.headed value
= value` in `SpelledOne`, met from `HeadedStatement`) and the
re-estimate (E2 40-45, glue 8-13) are in `SKETCH.md`, "After lane 3".

**Not done:** E2's blocks, lines, declarations and `if` outside
brackets; the glue.

**Friction** (beyond parts 1 to 16):

81. A constructor pattern with a record pattern as a non-last argument
    (`Bracketed { above, after } inner close`) is a parse error that
    names the fix (`({ … })`), but the file's other 400 warnings
    (`W-ARROW-FORALL`, as in 76) buried it again.
82. `givesDone _ holds proof` inferred the value from the proof's type
    where the predicate ignores part of the value (`HeadedExpr` of a
    `Negate` is its operand's), and failed far from the cause; naming
    the value fixed it.
83. Good: 50 theorems cloned from `ShapeProofs.sw` with a different
    predicate checked after two errors; `placedBelow` and
    `declarationsRun` (with its 28-deep pattern) checked first time.
84. `stitchwort test` said "103 from the cache" after `bareStatement`
    changed (`--no-cache` then ran and passed all 103). Either the
    cache key misses a changed definition the tests reach, or it is
    cleverer than I know; worth a look.

### Part 18 (Fable, 16 Nov 2026): E2 and the glue; the driver formats with no check (lane 4 of 6)

`spellsFile` is proved (`Fmt/BlockSpellProofs.sw`, 56 theorems), so
`printParses`, `formatDirectRoundTrip`, `formatDirectIdempotent` and
`formatAgrees` rest on nothing unproved. `formatDirect` and those
theorems are in `Toy.Fmt` (`Format.sw`, `Fmt/DirectProofs.sw`), the
driver's `formatFile` calls `formatDirect`, and the file loop's theorems
(`Fmt/Proofs.sw`) are about it. The sketch project is gone. Audit: 1272
theorems, 0 failed; `stitchwort test --no-cache`: 105 passed (the 103
and the sketch's two probes); `toyfmt_formats_a_folder_under_run_and_built`
passes.

The statements and how they fit are in `SKETCH.md`, "After lane 4".
What the top theorems say, with nothing assumed:

- `printParses`: `parse source = Ok file` gives `parse (file.print
  width).text = Ok file`, at every width.
- `formatDirectRoundTrip`: the output is the source's tree printed, and
  parses to that tree.
- `formatDirectIdempotent`: `formatDirect output.text width = Stable
  output`.
- `formatAgrees`: `format source width = formatDirect source width`.

**Not done:** the checked `format` is still there (the tests use it);
`Rules.sw` and `Cli.sw` say nothing of a run-time check (searched);
docs outside `tools/toyfmt` were not searched.

**Friction** (beyond parts 1 to 17):

85. Three of my new names (`Closing`, `Opens`, `Joins`) were already
    defined in `JoinProofs.sw`, same namespace, another file. The
    checker reported the clash as about 40 type errors in the older
    file and none at the new definition; "defined twice" at the second
    one would have saved two rounds.
86. Good: the 1,400-line mutual induction (`exprOut`, `bodyOut`,
    `linesOut`) and `declarationsOut` (a 40-deep `Both` chain) checked
    with no type error once the brackets balanced; every error in this
    part was a bracket count or a name clash. A bracket-balance hint
    per `match` arm would have found each in one round.
87. Whether `[x, ..xs ++ ys]` and `[x, ..xs] ++ ys` are the same to the
    checker (they are) decided how every motive here is written; the
    proving guide could say so.

Tidy-up (SW-3436, SW-3458, SW-3469): deleted `printJoins`, `joinedLex` (with its only user `joinedLexExample`), `printedLexes`, `parsedPrintLexes`, `printedPlaces` and `printedOr`; renamed `Scan.Waiting` to `Scan.Pending` and the disturber's `Chunk` type to `LineGroup`.


SW-3484: the checked `format` was deleted and `formatDirect` renamed to `format`.

SW-3486: `FormatResult` is now `Formatted`/`ParseError`, `Printed` is gone (`SourceFile.print` returns `Text`), and lemmas named for `Stable`, `Refused` or `Printed` are renamed (`formattedInjective`, `formatFileParseError`, `formatFileWriteError`).

SW-3488: the driver's `Outcome.Formatted` is `Outcome.Done`, so `FormatResult.Formatted` is written unqualified (`Formatted`) everywhere; `ParseError` was already unqualified.
