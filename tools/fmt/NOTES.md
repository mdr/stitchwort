# The self-hosted formatter: notes

The plan is `docs/proposals/self-hosted-fmt.md`. Each stage ends with a section here: its harness count, its speed numbers and friction.

## Stage 0 (SW-3772): the comparison harness

Sonnet, 17 November 2026.

### What is here

| Piece | Where |
|---|---|
| The harness | `dev/fmt-twin` (Python), run as `task fmt:twin STAGE=... INPUTS=...`; documented in `docs/testing.md`, "The formatter twin harness" |
| The Rust token dump | `stitchwort dev tokens FILE` (`crates/cli`, `stitchwort_fmt::tidy::token_dump`): one line a token after rule N |
| The fuzzer's programs | `FUZZ_WRITE_DIR=DIR` on `crates/fmt/tests/it/fuzz.rs`'s test writes each case that parses to `DIR/case-N.sw` |
| The stub | `tools/fmt/src/Fmt/Twin.sw`: `Fmt.Twin.main`, `fmt --stage STAGE FILE...` or `--batch LIST`, copies each file to standard output whatever the stage |

The executable's protocol: `EXE --stage NAME FILE` prints the stage's answer on standard output. For a file the Rust side refuses it prints nothing there, writes the first line of the message to standard error, and exits non-zero. The harness compares the exit status, standard output, and (when refused) that first line. `EXE --stage NAME --batch LIST` (SW-3774) answers for every path in LIST in one process; each block is a line `\x1ePATH`, a line `\x1fSTATUS\x1fLENGTH\x1fMESSAGE`, then exactly LENGTH characters of standard output. A refusal is one block among the others, so it doesn't stop the run; the batch exits 0 even when a file was refused. The harness uses batch mode by default, in `--jobs` parallel chunks, and `--no-batch` keeps the one-process path. The Rust side's answer, per stage:

- `tokens`: `dev tokens`'s lines (`Kind "text" col=C line_start=B blank=N leading=[col:blank:"text" ...] trailing=none|col:0:"text"`, then `EOF blank=N leading=[...]`). A refusal is `error: MESSAGE` on standard error, status 1.
- `tree`: `dev tree --print`'s tree without its `PATH:` header and totals line. A declaration that doesn't parse is an `Error` node in the dump, status 0, so refusal isn't separate here.
- `refusal`: status 0 and no output if `fmt -` formats the file; else its status (2) and the first line of its message (a `[E-PARSE]` line).
- `text`: the formatted text of `fmt -`, or the refusal as above.
- `passes`: not built yet.

### The gate [measured, Speedwell, load about 5]

The stub (copies its input) on `--stage text`:

| Input | Identical | Time |
|---|---|---|
| golden `before` files (unformatted) | 0 of 62 | 1.1 s |
| golden `after` files (formatted) | 62 of 62 | 0.8 s |
| 17 named repo files (Toy.Fmt, std List, `aoc/src/Aoc/Common`, the stub) | 17 of 17 | 0.4 s |
| fuzzer seed 5, 100 cases, comment rate 0.2 (79 parse) | 21 of 79 | 1.2 s |
| disturbed `goldens-after`, seed 3 | 10 of 62 | 1.0 s |

(The times are the executable's; the Rust answers were computed first, 10 to 20 s for the fuzzer seed including building its test binary.) The whole repo and the old layout were not run in the lane: they are broad runs for the verifier.

### Batch mode (SW-3774)

The executable answers many files in one process (`--batch LIST`), and `dev/fmt-twin` uses it by default in `--jobs` chunks. On this checkout, `tokens` over `goldens` agrees with `--no-batch` (both 0 of 124: the stage 0 stub copies its input, while `dev tokens` prints token lines; `text` is the stage where the formatted half matches, 62 of 124 in both modes). On 100 sampled repo files, `tokens` took 0.2 s in batch (the executable's own time; 0.3 s for the group with the Rust answers cached) against 1.4 s one process a file (0.8 s for the group). A 500-file sample took 0.2 s in batch (4.6 s for the group while 400 Rust answers were still uncached, and 0.4 s with all 500 cached), so the executable is comfortably inside the 15 s target for the full repo. `--self-test` checks the block parser on a crafted batch with a refusal in the middle.

### Not done, for later stages

- Stage 4's pass-by-pass dump (a `dev` command after `passes::run`): `fmt-twin passes` stops with a message.
- The Toy++ fuzz inputs (`tools/toyfmt/plus/inputs/*.sprig`) are Sprig programs, not Stitchwort: translating them is not trivial (different keywords, `takes`, typed groups), so they are a follow-up. The comment probes could be written as Stitchwort files under the fuzzer's `FUZZ_COMMENTS`, which the `fuzz` input already supports.
- The disturber is a few conservative line-level changes (doubled spaces, indentation ×2 or ×3, trailing spaces and blank lines between declarations), one chosen per file from the seed. Where it breaks the parse, the Rust side's refusal is the answer to match. The proposal's token-level disturber (spans from the real lexer) is not done.

## Stage 1 (SW-3808): the lexer and rule N

Opus, 17 November 2026.

### What is here

| Namespace, file | What | Rust counterpart |
|---|---|---|
| `Syntax`, `Syntax/Token.sw` | `Tok` (one constructor per Rust `Tok` variant, `Tok.name` for the dump), `Comment`, `Trivia`, `Token`, `Lexed`; the keyword and Unicode-alias tables as text and character patterns | `lexer.rs`'s types |
| `Syntax`, `Syntax/Lexer.sw` | `lexemes`: `Parse` over characters, every character in a lexeme; `assemble`: a fold that gives each token its column (in bytes), `lineStart` and trivia; `lex` | `lex_with_trivia` |
| `Syntax`, `Syntax/Settle.sw` | rule N, `Lexed.settled`: five passes in the Rust order, the backward ones on a newest-first list of the leaves already settled | `tidy.rs`'s `place_comments` |
| `Syntax`, `Syntax/Tree.sw` | the tree's token layer: `Leaf` (a token with its trivia) and the dump's lines in `dev tree --print`'s form | `tree.rs`'s `dump` |
| `Syntax`, `Syntax/Dump.sw` | `dev tokens`'s lines; Rust's `{:?}` quoting; how an error names a character | `token_dump`, `shown` |
| `Syntax.Tests` | the `tidy.rs` tests ported, and lexer cases | |
| `Fmt.Twin` | `--stage tokens` from the real lexer, single-file and batch; the later stages are still the stub | |

`Syntax` is one namespace over several files, as the toy's `Toy.Syntax`
is, so stage 2's parser and tree types join it without imports; `Fmt`
is for the formatter proper (passes, rules, the driver). Proofs go beside
each file (`Syntax/LexProofs.sw` and so on), as in the toy.

Shapes chosen for the proofs (stage 8), none proved yet:

- The lexer is the toy's two layers: lexemes that cover the source (so a
  `covers` theorem can follow the toy's `lexCovers`), then a fold. The only
  recursion outside `Parse`'s own combinators is `Parse.recursiveWith` for
  the `${…}` nesting, and fuel from `Parse.mark().left` for a text
  literal's pieces and a qualified name's components.
- A lexical error is `Parse.fatal` with the Rust message, so no choice can
  back up past it and the refusal is exactly the Rust one.
- Rule N's passes are each structural on the leaves left (`homeFrom`,
  `commasFrom`, `arrowsFrom`, `letsFrom`) with an accumulator, as the toy's
  `homeStep` and `carryForward`. The searches Rust does by index (a record
  update's `|`, an expression `let`'s `:=`) walk the settled list back and
  the rest forward, only for the few tokens that need them.

### The gate [measured, Speedwell, load 12 to 18]

| Input | Identical |
|---|---|
| `goldens` (both files of each pair) | 124 of 124 |
| `repo`, `--sample 300` | 300 of 300 |
| `fuzz`, `--fuzz-cases 300` (240 parse) | 240 of 240 |
| `disturbed` (from `goldens-after`) | 62 of 62 |
| 70 hand-written edge cases (scratch, not committed), 47 of them refusals: every lexical error, `"""` texts and their error order, CRLF, Unicode columns and quoting | 70 of 70 |

None of the harness's groups has a file that doesn't lex, so the refusals
were checked with the hand-written cases: tabs, unclosed strings,
characters, `"""` texts and `${…}`, each bad escape, `@`, unknown ASCII and
Unicode characters (named, unnamed, invisible), and the order the Rust
lexer reports two errors in a `"""` text (an error inside a `${…}` first,
then a tab in the indentation, then a bad escape). Everything matched on
the first run of the harness; the one difference before that was the
whole token list reversed (the `|>` finding below).

### Speed [measured, Speedwell, load 12 to 18, so high]

On 300 sampled repo files (1.07 MB), one process, `--batch`:

| Up to | Time | Per MB |
|---|---|---|
| reading the files and `toList` | 0.03 s user | |
| the lexemes (`Parse`) | 1.34 s | 1.3 s/MB |
| the tokens with trivia (`assemble`) | 1.43 s | 1.35 s/MB |
| rule N | 1.49 s | 1.4 s/MB |
| the dump (`--stage tokens`) | 2.1 s | 2.0 s/MB |

Peak memory 60 MB. §5 plans 2.5 to 3.5 s/MB for the whole formatter, so
lexing alone at 1.3 s/MB is about half of it: worth a profile in stage 7
(or earlier, if stage 2's parse rate is close to the line). Almost all of
it is `Parse`'s handler: a lexeme costs about six operations (`mark`,
`span`, `mark`, and `many`'s round), and spaces are lexemes of their own.

### Friction

- **`x |> f a` is `f x a`, and I wrote it believing `f a x`.** `arrows
  leaves |> letsFrom []` type-checked (both arguments are lists) and
  reversed the whole token list. `docs/syntax.md` says it plainly ("the
  value on the left becomes the first explicit argument"); what misled me
  was the Rust lexer's own doc comment on `Tok::PipeGt`: "`x |> f a` is `f
  a x`", which is wrong. Finding: fix that comment.
- **A failing `test` says only "evaluated to False".** Finding where the
  list got reversed took four extra tests; `a == b` failing could show both
  sides, as Rust's `assert_eq!` does.
- **No hexadecimal in std.** The messages need `U+D800` and the dump
  `\u{1f}`; I wrote `hexDigits` with fuel. A `Nat.toTextBase` (or
  `toHex`) is all that was missing.
- **No Unicode tables.** Rust's `{:?}` escapes characters that aren't
  printable or that extend a grapheme, from tables std doesn't have.
  `escapedAbove` is an approximation by block; it covers every case in the
  sample, the fuzzer's programs and the hand-written ones, but a string holding, say, a Devanagari vowel sign
  would quote differently. The Rust dump could quote comments and strings
  itself in a form Stitchwort finds easy (only `"`, `\`, controls), which
  would take this off the formatter's path entirely.
- **Columns are bytes in Rust, characters in `Text`.** The fold carries a
  byte count (`Char.utf8`'s length per character, only for lexemes that
  aren't ASCII). Fine, but a `Text.utf8Length` on a slice is a list walk.
- **A rebuilt list isn't smaller.** `homeFrom behind [next', ..later]`,
  with `next'` the next leaf changed, isn't seen as terminating; passing
  the change on as a parameter (`bumped`) fixed it. The message and its
  note said exactly that.
- **`Parse` fitted a lexer well**: `Parse.fatal` for errors that must not
  back up, a parser that `stop`s to end a `many`, and `recursiveWith` for
  `${…}` inside `${…}`. Mutual recursion through a fuelled helper
  (`item` → `textLiteral` → `pieces` → `self`) checked without help.
- **`Char` is closed to programs** (`E-STD-NAMESPACE`), so a helper on
  characters is a plain function; the error says so and suggests it.

### Left for stage 2

- The parser on `Parse` over the settled leaves (or `Parse.Located` leaves,
  as the toy's tokens are), with the tree types per construct family in
  `Syntax`, each with a `dump (depth)` built from `nodeLine` and
  `Leaf.treeLine`, and `--stage tree` and `--stage refusal` in `Fmt.Twin`.
- A profile of the lexer, if stage 2's timing makes it matter.

## Stage 2a (SW-3819): expressions and patterns

### What is here

- `Syntax.Expr`: the tree's expressions and patterns, and their dump in
  `dev tree --print`'s form (each node gives a list of lines, joined once:
  building one text from the next node's text copied a long list's tail
  per item and made a 3,000-item list 8 times slower than a 1,000-item
  one).
- `Syntax.Parser`: the parser on `Parse` over stage 1's settled leaves,
  following `crates/syntax/src/parser.rs` function by function (`expr`,
  `block`, `cmp_expr`, `app`, `atom`, `match_expr`, the pattern levels…),
  total: fuel from `Parse.recursiveWithFuel` and from the items left, no
  `partial`. It never backs up: lookaheads are pure functions over the
  items left, and every error is `Parse.fatal` with the Rust message.
- `stitchwort dev tree --expression FILE` (Rust): the file read as one
  expression (`parse_expression_tree`), dumped under an `Expression` root,
  or `error: …`. `dev/fmt-twin expr` and `fmt --stage expr` compare the
  two. `--stage tree` and `--stage refusal` stay stubs: they need
  declarations (2b).
- `Syntax.Tests.Exprs`: the layout rules and the tree's shape on small
  cases.

### The tree's shape (from SKETCH.md §1 and the SW-3824 follow-up)

- Leaves are `Word`s, text and `Comments` (own-line notes above, each with
  a `blankBefore` flag, and a trailing comment): no column, no line start,
  no blank-line counts. The parser reads `Item`s, which keep the layout
  (column, line start, bracket depth, the line's indent, `glued`) for the
  layout rules, and drops it when it builds a node. Nothing in the dump
  needed a column.
- Commas aren't kept: a list has its items and `trailingComma`; the dump
  writes the `,` lines back, and one before a list pattern's tail or a
  record pattern's `..` when there are items.
- Shapes with tags: `Infix InfixKind` (Binary, Membership, Range, Pipe,
  Arrow, Iff, Seq), `Binding BindingKind` (lambda, `∀`, `∃`), `Facts
  FactsKind`, and `Atom (kind: Tok)` / `PatternWord (kind: Tok)` for a
  token on its own. `Paren` is its own constructor; `(f) x` is an `App`
  with a `Paren` head.
- Folded in from the sketch: 1, 2, 3, 7, 11, and 5 for this subset (no
  error, gap or derived nodes). Not done, for 2b: 6 (a traversal), 8 (one
  parameter-group constructor: `Param` has four, as the dump's node kinds
  do), 9 (`∀` as `Option Comments`: kept as a `Word` here, since the dump
  prints `∀` or `forall` as written), 10 (fixed tokens as `Comments` only:
  the dump prints each token's spelling, and `→`/`->`, `∧`/`&&` differ, so
  matching the dump wins until the dump normalises them), 12 (the
  or-pattern check is done while parsing, not as `SourceFile → Option
  Text`: Rust does it in its lowering, so the messages differ only when a
  later syntax error follows), 13 (fuel is `2 * left + 2`, since a level
  hands over to another without reading).

### Layout

Continued lines are read as Rust reads them: `expr` opens a block at a
line's column when the line starts further right than the enclosing block
(or at its column, a block of one line); `Modes.stops` is `is_stop`
(a line at or left of the block's column ends what is read, unless it
closes or continues a bracket or starts with an infix-only operator at the
column); `then`/`else`, `|>` lines and `match` arms (which must line up)
follow their own rules; a line can't start with `.method`. A block of
several lines, a block's `let` and local definitions are `notYet` (2c).

### The gate [measured, Speedwell, load 15 to 37]

Files read as one expression, through `dev tree --expression` and `fmt
--stage expr`, all identical but for "not parsed yet":

| Set | Files | Identical | Not parsed yet |
|---|---|---|---|
| Corpus: every expression body, match arm and pattern in the repo's `.sw` files, one per file | 22,373 | 21,135 | 1,238 (`rewrite` 1,127, `calc` 57, `let` 21, `cases` 21, function types with named parameters 7, `match induct` 4, effect row 1) |
| Broken: each of those cut or with a token swapped (refusals) | 2,032 | 1,925 | 107 |
| Hand cases (precedence, sections, patterns, messages) | 82 | 82 | 0 |
| Continued lines | 20 | 20 | 0 |

The generators are scratch scripts, not committed (no repo bloat): the
corpus takes each `:=` body, arm and pattern that fits on a line.

### Speed [measured, Speedwell, load 15 to 37, so high]

7,709 expression bodies in one bracketed list, 333 KB, dump identical to
Rust's: 2.1–2.5 s, of which lexing and rule N 1.0–1.15 s; so about
**3.5–4 s/MB for the parser and the dump**, 6.5–7.5 s/MB in all. The
same in 78 files of 100 items: 2.0 s. Rust: 0.06 s. Linear from 1,000 to
7,709 items after the fixes below. This is dense input (no comments, no
blank lines, no declarations), so real files should do better per byte,
but it is over §5's 2.5–3.5 s/MB for the whole formatter: 2b should time
whole files and profile before changing anything (the lexer alone is
about half of it).

### Friction

- **`List.length` in fuel is quadratic.** `left().length + 1` as fuel at
  every list and `done.length` in the comma loop made a 3,000-item list
  take 10 s; `Parse.mark().left` is O(1). Nothing warns, and the toy never
  had inputs long enough to show it.
- **Text built by nested interpolation is quadratic** for a long list
  (above). A dump wants a list of lines, or a builder.
- **Constructor names share one namespace with `Tok`'s**: `Arrow`,
  `Pipe`, `Word` clashed, hence `InfixArrow`, `Atom`.
- **Keywords can't be field names** (`type`, `with`, `then`):
  `annotation`, `withKeyword`, `accepts`.
- **No effects in a guard**, and a `match` can't be lifted out of a
  lambda: bind with `let` first, or move it to a function.
- **Termination through a record field** (`fields.fields`) needs the
  record destructured in the pattern; mutual recursion between pattern
  functions needed one more level through `pself`.
- **`build --native` needs a `native` build of the CLI**: the worktree's
  release binary had none, so the twin was built with main's.

### Left for 2b and 2c

- 2b: declarations, headers and types (function types with named
  parameters, effect rows), so `--stage tree` and `--stage refusal` can
  run on whole files; the sketch's items 6, 8, 9, 10 and 12; a timing on
  whole files.
- 2c: blocks of several lines, `let`, local definitions, `handle`,
  `calc`, `rewrite`, `cases`, `match induct`/`reify` (each a `notYet`
  today).
