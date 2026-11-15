# The toy formatter: every moving part, at a small size

**Status:** proposed, 15 November 2026 (SW-3339, for D3579's "then a toy
language's formatter"). Paper lane: nothing is built. The probes were
throwaway `.sw` files run with the main checkout's release binary (built
08:02 today). One question for Matt, [D3606](#d3606-blocks-by-indentation-or-by-braces).

Claims are marked **[measured]** (Speedwell, load 4–8, one run each),
**[ran]** (a probe that checks or runs today) or **[estimated]**.

## In plain words

**What it is.** A small made-up language, *Sprig*, and a formatter for it
written in Stitchwort: `toyfmt`, a built executable you point at a folder.
It reads every `.sprig` file, lays each one out afresh (choosing the line
breaks itself, as `stitchwort fmt` does), and writes back the files that
changed. Sprig is about a page of grammar, but it has the shapes that make
formatting hard: operators with precedence, blocks by indentation, long
calls and lists that must break, comments that must be kept, and strings
that can't be split.

**What it proves.** That every part the real Stitchwort formatter
([self-hosted-fmt.md](self-hosted-fmt.md)) stands on exists and works
together, before 40–60 lane hours go into it: reading, writing and listing
files from a program (`Files`), cutting text cheaply (fast `Text`), lexing
then parsing with the library's parser (`Parse.tokens`), keyword tables as
`match`es on text, a layout engine of the Rust formatter's kind, the
theorems the plan promises (output parses back to the same tree; formatting
twice changes nothing), and a real executable with flags and exit codes.
Each part gets a test that would fail if the part were missing or broken.
It also measures speed on 1 MB of input, so the real plan's 20-second
estimate rests on a number rather than a guess.

**What it doesn't prove.** That Stitchwort can match the Rust formatter
byte for byte, which is the real project's whole difficulty (94 node kinds,
the rewrites, the Rust parser's exact tree). Nor that a 9,000-line program
checks quickly. It is a dress rehearsal for the parts, not for the size.

**Cost.** About 12–16 lane hours in four stages [estimated], starting when
fast text (T1, SW-3337) and Files (F1, SW-3338) land.

## 1. Sprig

Sprig is Stitchwort's shape in miniature: declarations at column 0, `=`
then a body, blocks by indentation, `--` comments, the same precedence
style. Every printing rule below is a Stitchwort rule from
[formatter-style.md](formatter-style.md) with the same decision in it.

```
file    = { decl }                                   -- each decl starts at column 0
decl    = "fn" NAME "(" [ NAME { "," NAME } ] ")" "=" body
        | "let" NAME "=" body
body    = expr                                       -- on the same line, or below
        | block
block   = stmt { stmt }        -- statements start lines at one column, deeper than
                               -- the line that opened the block; deeper lines continue one
stmt    = "let" NAME "=" body | expr
expr    = "if" expr "then" body "else" body | binary
binary  = unary { OP unary }   -- levels, loosest first: ||  &&  == != < <=  ++  + -  * / %
unary   = "-" unary | postfix
postfix = atom { "(" [ args ] ")" | "." NAME }
args    = expr { "," expr }
atom    = NUMBER | STRING | NAME | "(" expr ")" | "[" [ args ] "]"
STRING  = '"' { any char but '"', '\' or a line break | '\"' | '\\' | '\n' } '"'
comment = "--" to the end of the line, on its own line or after code
```

An example, already formatted at width 60:

```
-- Totals for one order.
fn total(order, rates) =
  let base = sum(order.items.map(price))
  let tax = base * rates.tax / 100

  if base > rates.threshold then base + tax - discount(order, rates) -- loyal
  else base + tax

let names = ["alpha", "beta", "gamma", "delta", "epsilon", "zeta",
  "eta", "theta"]
```

**Printing rules** (the toy's style sheet, each tied to the real rule):

| Rule | Sprig | Stitchwort's |
|---|---|---|
| P1 | Every construct is a group: one line if it and what must follow it fit, else every break in it breaks | E1 |
| P2 | Header parameters: one line, else one a line at +4, `) =` back at the header's column | E2's 4 for headers; D1012 closer |
| P3 | Body after `=`: on the header line if it fits, else one line below at +2, else broken below; a block of two or more statements always below | S12, D3571 |
| P4 | Call arguments: one line, else one a line at +2 with `)` at the call's line | S23 base case, D3567 |
| P5 | List items fill their lines | D3572 |
| P6 | An operator chain at one level breaks before every operator at +2; tighter levels are their own groups; brackets kept as written | S27 |
| P7 | `if`: one line, else `if c then a` / `else b` at the `if`'s column, a branch that doesn't fit goes below at +2 | S19 |
| P8 | An own-line comment sits above its item at its indentation; a trailing one stays after one space; both force their group to break. A comment anywhere else leaves its declaration as written, counted | S38–S40 |
| P9 | Blank lines kept, as one, between declarations and statements; dropped elsewhere | E4 |
| P10 | Strings and names never split; a line that can't fit stays long; width counts characters (`→` is one) | E5 |

The width is a flag (default 80), so tests can use small widths.

## 2. The moving parts

| Part | What the toy uses | Test that proves it |
|---|---|---|
| **Files** (F1) | `Files.read`, `write`, `list`, `info`; `Path`; `FileError` values; the driver `formatPaths: List Path → {Files} Report`; a walk of its own over `list` with a depth bound (`Files.walk` is F3) | Under `Files.simulate`: an unformatted file is rewritten; a formatted file is left alone *and not written* (a pass-through handler counts `write`s, so the test also exercises a handler over `Files`); a missing path and an unparsable file are reported as values, leave the disk unchanged, and the other files are still done; `--check` writes nothing |
| **Fast Text** (T1) | The lexer records offsets (`Parse.located`); names, numbers, strings and comments are cut from the source with `Text.slice`; lines are built with `++` and `Text.concat`; widths are `Text.length` | `slice` round trip: the tokens' and trivia's slices, concatenated, are the source (a run-time check whose failure is a bug, plus a test on awkward text: `→`, a combining accent, U+10FFFF). Timing on 1 MB (§4) |
| **Text patterns** (SW-3284) | Keyword table `match word with \| "fn" => Some Fn …`; operator table `\| "&&" => Some And …` | Tests on each table; the cheap theorem that a `Name` token is never a keyword (`cases`, through the catch-all's equations) |
| **Generic Parse over tokens** (SW-3283) | A `{Parse Char}` lexer giving `Parse.Located Token`; a `{Parse (Parse.Located Token)}` parser with `Parse.one`, `chainLeft` per level, `recursive`, `sepBy`; `Parse.tokens` for messages | Exact messages, for example: `fn f(a b) =` gives "line 1, column 8: expected ',' or ')', got 'b'"; an unclosed string a lexing message; "got the end of the input" |
| **Layout** | Blocks: each token records whether it starts a line and at what column (from its own leading trivia); the parser passes the block's column down as an argument, as the twin's parser passes its modes (self-hosted-fmt.md §2) | A statement indented further continues; one indented less ends the block; re-indenting a block in the disturber never changes the tree (below) |
| **Layout engine** | `Toy.Doc`, a port of the core of `crates/fmt/src/printer/engine.rs`: `Text`, `Line`, `SoftLine`, `HardLine`, `Blank`, `Nest`, `Group`, `Concat`, `Fill`, `Choice`, `LineSuffix`, `BreakParent`; total by fuel (the document's size) | The Rust engine's own tests ported, six of its eight (not the two on `Verbatim` and `LineStart`); 12 golden pairs, one per rule P1–P10 plus two mixed |
| **The printer ignores the author's layout** | A disturber in the test file: from a seed, re-indent within the layout rule, double or squeeze spaces, join and split lines inside brackets, add blank lines inside expressions | For 50 seeds over the goldens' outputs: format(disturb(out)) = out. This one test covers idempotence and layout independence on real shapes |
| **Proofs** (§3) | Validation in `format`; the erased tree as the rules' input type | `formatRoundTrip`, `formatIdempotent` and `lexCovers` checked; `task audit:touched` clean |
| **Built executable** | `stitchwort build --native tools/toyfmt`; `main(): {Console, Files, Fail}` (or today's names until G2) | One end-to-end test: copy a fixture folder (formatted, unformatted, broken, a nested folder, a `.txt` to ignore) to a temporary folder, run `toyfmt` there with `stitchwort run` and as the native executable, compare the folder and the exit code with the expected ones |
| **CLI** | `toyfmt [--check] [--width N] PATH…`: folders are walked for `.sprig` files; changed paths on standard output, problems on standard error (`IO.printError`, F1); exit 0, or 1 through `Fail` when anything would change (`--check`) or failed | In the end-to-end test: `--check` on a formatted folder exits 0 and writes nothing; on an unformatted one exits 1 and names the files; a bad flag exits 1 with a usage line |

**Where it lives** (the orchestrator's call): `tools/toyfmt/`, a project
with its own `stitchwort.yaml`, namespaces `Toy.Syntax` (token, lexer,
tree, parser), `Toy.Doc` (the engine), `Toy.Fmt` (rules, check, driver,
`main`), with `NOTES.md` for friction. The end-to-end test is one nextest
test beside `crates/driver/tests/run.rs`, skipped where there's no C
compiler, so the tiers run it and a lane can run it by name in seconds.
The toy's sources join the repo's `stitchwort fmt` set; nothing generated
is committed (the 1 MB input and the disturbed files are made at run time).

## 3. Proofs

The real plan's §7 promises two theorems "by construction". The toy is
where that technique is tried for real, on a small tree, before 9,000
lines depend on it.

- **`lexCovers`** (cheap, worth it): `lex source = Ok tokens` gives
  `Text.concat (pieces tokens) = source`, where `pieces` are each token's
  trivia and text slices. Proved by validation: `lex` checks this before
  answering, so the theorem unfolds `lex` and uses the check's decision.
  This is T1's `sliceAppend` exercised by a user. Half a day [estimated].
- **`formatRoundTrip`** (cheap, worth it): `format source = Stable output`
  gives `(parse output).map erase = (parse source).map erase`, where
  `erase` keeps kinds, token texts, comments and kept blank lines. By
  validation, as self-hosted-fmt.md theorem 1. A probe of the same shape
  on a stub tree reached its last step in eight lines and stopped there
  [ran]: `cases` turns `Stable x = Stable y` into `x = y` but doesn't then
  rewrite the goal with it, so even `f x = f y` stays open [ran]. By hand
  it is a `match` on the decision and an `Eq.cong`. Half a day.
- **`formatIdempotent`** (the one that matters): the rules take the erased
  tree as their input type, so the output depends only on it by typing; with
  `formatRoundTrip`, `format output = Stable output`. Self-hosted-fmt.md
  theorem 2 in miniature. One day [estimated]; if it is much harder here,
  the real plan's estimate of 1–2 days is wrong, which is worth knowing now.
- **Optional, a showcase:** formatting a folder twice gives the disk that
  formatting it once gives, from `formatIdempotent` and `Files.simulate`'s
  laws. About a day, if induction over the file list goes as F1's laws
  suggest (SW-3257 is the known friction).
- **Not worth it:** `parse (print tree) = tree` from the rules (weeks, and
  the real rules differ); the engine's tidiness beyond a test.

## 4. Speed

Measured today, before T1, with a probe lexer (`Parse.located`,
`oneOf`, keywords by text pattern) on 990 KB of Sprig-like lines
[measured]: about 3.5 s with `stitchwort run` after subtracting checking,
and 1.8 s as a native executable. That agrees with generic-parse.md's
1.9 s/MB, where lexing then parsing took 3.5 s/MB native.

T1 won't change the lexer's own loop much: `Parse Char` reads a
`List Char`, which `Parse.tokens` makes with `input.toList`. What T1 changes
is everything after: cutting token texts, `length` in the engine (today a
recount per call, SW-3254) and building output. Reading the characters
from the text itself is D3597's direction, built later; the toy's timing is
the evidence for when.

**What the toy reports** (not a gate): seconds per MB native and on the
machine for lexing, parsing, printing and the whole format, on a 1 MB file
generated at run time and on 100 KB, so linearity shows; peak memory. A
rough expectation is 4–8 s/MB native for the whole format [estimated from
the above]. At that rate the real formatter's 6.5 MB would take 25–50 s
with combinators, against the plan's 20 s; a hand-written lexer (0.11 s/MB,
self-hosted-fmt.md) closes most of that, which is what the plan already
assumes for the twin. The toy says by how much.

## 5. What it leaves out, and what scaling up adds

Left out on purpose: byte-for-byte agreement with anything; the rewrites
(`∀`, brackets, merged parameters); `match`, handlers, lambdas, named
arguments and the hug; `Align`, `IfBroken`, `Verbatim` (except for P8's
fallback) and text blocks in the engine; error recovery; JavaScript and
the playground (F2); speed work.

| Scaling up adds | Where in self-hosted-fmt.md | What the toy hands it |
|---|---|---|
| The comparison harness against the Rust formatter | stage 0, §6 | the disturber; the end-to-end test's shape |
| A lexer with the Rust lexer's tokens and trivia | stage 1 | the trivia design (each token's comments, blank lines, line start); slices; the speed numbers that decide combinator or hand-written |
| A parser giving the Rust lossless tree | stage 2, §3 | layout by passing the block column; whether `Parse` is pleasant enough to reconsider §3.2's "hand-written" |
| The engine and 94 kinds' rules | stages 3–4 | `Toy.Doc` grows into `Fmt.Doc`: the ported tests and the core already there |
| Rewrites, the safety check, left-as-written | stage 5, §3.4 | the validation pattern and `Stable` |
| Speed | stage 6 | the per-phase timings |
| Proofs | stage 7, §7 | theorems 1 and 2 already done once, and their real cost |

The batch stream (self-hosted-fmt.md §2) goes: the twin takes the toy's
`{Files}` driver.

## 6. Gaps seen today (tickets to file)

From the probes [ran]; the T1 and F1 items (`Text.concat`, `slice`,
`IO.printError`, `Files`) are left out as in flight.

1. **`cases` doesn't use the equation it derives.** From `h: Stable x =
   Stable y` (or `Some x = Some y`) it proves `x = y`, but `f x = f y`
   fails ("couldn't close the case"), splitting `x` and `y` as texts
   instead of substituting. Validation proofs hit this at once. (Opus,
   `cases` is a tactic, D2506.)
2. **A program's exit status is 0 or 1.** `Fail` gives 1; nothing gives 2,
   which `stitchwort fmt --check` uses for a file it can't parse
   [measured: 2]. A formatter, a test runner or any script wants to tell
   "would change" from "broken". Design ticket: an exit code from `main`
   (for example a `main` returning an `ExitCode`, or `Fail` with a code).
3. **Constructors of different types in one file collide even where the
   type is known:** a token kind `Str` and a document `Str` make `| Str t
   =>` in a `match` on a `Doc` `E-AMBIGUOUS` [ran]. A lexer and a printer
   in one program always meet this. Existing: SW-510 (resolve by expected
   type) and SW-2716; worth raising SW-510 before the toy's stage A.
4. **`Int.ofNat` doesn't exist and the note doesn't find `Nat.toInt`:** it
   suggests `OfNat`, `modNat`, `toNat` [ran]. A note for a missing
   `A.ofB` could name an existing `B.toA` (diagnostics, Sonnet).
5. **`Files.walk` is F3,** so the toy writes a bounded walk. Not a new
   ticket: F3's brief should start from the toy's walk.

## 7. Stages

Start when T1 and F1 have merged. Hours are lane hours [estimated]; each
stage adds to `tools/toyfmt/NOTES.md` (friction, timings).

| Stage | What | Model | Hours | Gate |
|---|---|---|---|---|
| A | Project skeleton; token type with trivia and line start; lexer (slices, keyword and operator tables as text patterns); tree and `erase`; the parser over tokens with blocks by column; the exact-message tests; the 1 MB timing of lexing and parsing | Opus (sets the project's shape; first friction notes) | 3–4 | message tests; `lex` coverage on the awkward texts; timings recorded |
| B | `Toy.Doc` and its ported tests (can start beside A); the rules P1–P10; the goldens; the disturber test; whole-format timing | Opus | 4–5 | engine tests; 12 goldens; 50 disturber seeds |
| C | The `{Files}` driver, the write-counting handler, the `Files.simulate` tests, the CLI, `main`, the native build, the end-to-end test | Sonnet | 2–3 | simulate tests; end-to-end on the machine and native |
| D | Proofs: `lexCovers`, `formatRoundTrip`, `formatIdempotent`; the folder theorem if wanted. The statements are checked by the orchestrator (D2436) | Sonnet; Opus if idempotence is stuck after 2 h | 3–4 | `task audit:touched -- Toy` clean |

Then a short report (Opus, about 1 h): what each part cost, the timings,
the friction tickets, and what it says about D3576 (start the twin's
stages 0–2) and about §3.2's hand-written parser. **Total: 13–17 lane
hours**, about 8–10 on Opus.

**Acceptance, in one list:** the tests in §2's table; the four tests of
§2's Files row pass under `Files.simulate`; the end-to-end test passes on
both runners; the goldens, the disturber and the proofs pass; the timings
and friction notes are written down; `toyfmt` formats its own fixture
folder twice with no change.

## 8. Questions for Matt

### D3606: blocks by indentation, or by braces?

*The problem:* Sprig needs some block construct. Stitchwort's blocks are by
indentation, which is the hard case for a formatter: re-indenting a line can
change what the program means, so the "parses back to the same tree" check
is doing real work. Braces (`{ a; b }`) make re-indentation always safe,
the parser simpler, and the check close to a formality.

*The change:* blocks by indentation, as in §1: each token records whether
it starts a line and at what column, and the parser passes the block's
column down. Braces would save about 2 lane hours [estimated].

*What it should do:* the toy then tests the part of the real formatter
most likely to go wrong silently (a statement printed at the wrong column
joining the line above), and shows whether `Parse`'s combinators can parse
a layout-sensitive grammar pleasantly, one of the reasons self-hosted-fmt.md
§3.2 gives for writing the twin's parser by hand. **[rec: indentation]**

The other calls (names, where it lives, the width default, the test's
location, how blocks are tracked) are the orchestrator's.
