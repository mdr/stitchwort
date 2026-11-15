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
  {Files, IO, Fail}`; `main` is `run IO.args()`). Changed paths go to
  standard output (`IO.print`), problems and "N declarations left as
  written" to standard error (`IO.printError`). It fails (exit 1) on a bad
  command line, a problem, or with `--check` a file that would change. Run
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

1. **No exit status but 0 and 1** (SW-3345). A formatter wants 0 = clean,
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

