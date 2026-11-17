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
- `passes` (SW-3863): `dev passes`'s `== P1 ==`, the tree dump, … `== P4 ==`, the tree after each tidy pass; a file that `fmt -` refuses is answered as in `refusal`.

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
  hands over to another without reading; stage 2b's notes say why
  `left + 1` is enough after all).

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

## Stage 2b (SW-3836): declarations, headers and types

Opus, 17 November 2026.

### What is here

| File | What | Rust counterpart |
|---|---|---|
| `Syntax/Decl.sw` | `SourceFile`, `Decl` (namespace, import, definition, data, ability, test), `Header`, `Group`, `Attributes`, `Row`, `Fields`, `Constructor`, `Operation`; their dump | `tree.rs`'s declaration `NodeKind`s |
| `Syntax/DeclParser.sw` | attributes, the parameter groups, `binder_type`, `result_type`, `row`, `pi_expr`, every declaration, `split_decls` and the file loop (`parseFile`), the codes of the few messages that aren't `E-PARSE` | `declarations.rs`, `data`, `ability`, the binders, `entry.rs`'s `parse_tokens` |
| `Syntax/Traverse.sw` | the traversal: one function per family that rebuilds a node from its traversed children, then applies a step (`onExpr`, `onPattern`) | |
| `Syntax/Lowering.sw` | the lowering's three checks as `Decl → Option Text`, called by `parseFile` after each declaration parses: or-patterns that bind, a parameter named twice, a guard on an arm with `()` and no body | `lower/patterns.rs`, `header.rs`, `matching.rs` |
| `Syntax.Tests.Decls` | shapes and the order of errors | |
| `Fmt.Twin` | `--stage tree` and `--stage refusal`, single-file and batch | `dev tree --print`, `fmt -` |

Function types with named parameters (`FunctionType`) and result types
with abilities (`Effect`, `Row`) joined `Expr`; `->`'s right side is now a
result type, as in Rust.

### The tree's shape

- **One parameter-group constructor** (sketch item 8): `Group` with a
  `kind` (`GroupParam`, `GroupBinder`, `GroupLambda`, the dump's `Param`,
  `Binder`, `LambdaParam`), `implicit`, attributes, `auto`, the names, the
  colon, the type and the default, each optional where a form lacks it
  (`()`, `[auto P]`). A lambda's typed group is `Grouped group`. The
  fourth node kind, `PatternTyped` (`((a, b): A)`), holds a pattern, not
  names, so it stays its own `Param` constructor.
- **Fixed tokens as `Comments`** (item 10, as the orchestrator decided):
  the new types hold a token with one spelling (keywords, brackets, `:=`,
  `:`, `=`, `|`, `@`, `.`, `as`, `auto`) as its comments, and the dump
  writes the text; a token with a choice (`->`/`→`, `∀`/`forall`) or a text
  of its own is a `Word`. Checked: `stitchwort fmt` keeps `forall`, `->`,
  `<=`, `&&`, `!` and their Unicode forms as written. Stage 2a's
  expression constructors still hold every token as a `Word`; converting
  them is a mechanical follow-up.
- No commas: `trailingComma` on `Attributes` and `Fields` (imports, rows
  and `unfolding` lists can't end with one).
- `DefKind` tags `def`, `theorem` and `instance`; a data type's root kind
  (`DataType`, `RecordType`, `TypeSynonym`, `Interface`) is derived from
  `isInterface` and the body, not stored.

### The file loop

`parseFile` splits the leaves into groups as `split_decls` does, parses
each group on its own items (as the Rust parser makes one `Parser` per
group, so a lookahead never crosses a declaration), then runs the
lowering's checks on it, and stops at the first error. That is the first
error in file order, which is `fmt -`'s first line: a later declaration's
error can't come before an earlier one's, and a lowering error replaces
only the parser's errors after it in the same declaration. The namespace
and import ordering rules are checked as the Rust loop does, before the
group is parsed.

A top-level `def` or `theorem` body is where the Rust parser recovers
from errors; the one message that changes there ("expected an expression,
but the line ends here") comes from a `recover` flag in `Modes`.

The tree stage answers only for files that parse: a file with a
declaration that doesn't (an `Error` node in the Rust dump, holding what
parsed before the error) is answered with status 1 and the message. The
strict parser has no partial nodes to dump (sketch item 5).

### Sketch items

- Done: 6 (the traversal), 8 (one group constructor, three of the four
  kinds), 10 for the new types, 12 (the lowering's three errors, called
  inside `parseFile`; the or-pattern check moved out of the parser, and
  `parseExpression` runs the same checks), 13 (below).
- Fuel (13): spike K4 (SW-3826) found the hand-overs between ladder
  levels are plain calls, not calls of `self`, so every recursion now has
  `Parse.recursiveWith`'s fuel, the items left and one more: each call of
  `self` or `pself` follows a read, so a call `d` deep has `d - 1` items
  behind it. Patterns did hand over without reading (`tupleComponent` to
  `PatternPlain`); that is now a plain call. Details in the proof plan,
  §11.
- Left: 9 (`∀` as `Option Comments`: kept a `Word`, since `∀` and `forall`
  are both spellings the formatter keeps); 10 for stage 2a's expressions.

### The gate [measured, Speedwell, load about 5]

The honest subset is the files whose every construct 2a or 2b reads;
"not parsed yet" names the first construct of 2c in a file.

| Input | Identical | Not parsed yet | Other differences |
|---|---|---|---|
| `tree`, `goldens` (124) | 78 | 46 | 0 |
| `tree`, `repo --sample 300` | 125 | 175 | 0 |
| `tree`, `fuzz --fuzz-cases 300` (235 lex) | 206 | 29 | 0 |
| `refusal`, the same three groups | 78, 125, 206 | 46, 175, 29 | 0 |
| `refusal`, 687 broken copies of 346 files in the subset (cut, a token deleted, swapped or inserted) | 683 | 3 | 1 |

So every file in the subset is identical: 409 in the tree stage, and 409
plus 683 refusals. The one difference is a mismatched bracket inside a
lambda's implicit group, `[a: (x: Type] a) => x`, where the Rust parser's
bracket table pairs `(` with `]` and reads a header group the Twin
doesn't. Over the 2,022 repo files outside the reject and repro folders,
972 (1.50 MB) are in the subset.

"Not parsed yet" by construct, in the sampled goldens and repo files (the
first in each file): a block's `let` 117, `rewrite` 61, `cases` 12, a block
of several lines 7, `handle` 7, a local definition 5, `calc` 5, an
expression `let` 4, `match induct`/`reify` 3. In the fuzz cases: a block's
`let` 11, `rewrite` 7, a local definition 4, a block of several lines 2,
`match induct` 2, `cases` 2, `handle` 1. 109 of the fuzz cases are
comments only (no tokens); the harness's tree for those is now empty, not
one blank line (`dev/fmt-twin`).

### Speed [measured, Speedwell, load about 5]

The 972 subset files, 1.50 MB, one process, `--batch`:

| Stage | Time | Per MB | Peak memory |
|---|---|---|---|
| `tokens` (lex, rule N, the token dump) | 2.55 s | 1.7 s/MB | 31 MB |
| `tree` (lex, rule N, parse, lowering checks, the tree dump) | 4.5 s | 3.0 s/MB | 48 MB |

The largest file in the subset (`std/Omega/Omega.sw`, 31 KB) takes
0.11 s, 3.5 s/MB with the process's start, so nothing grows faster than
linearly. Whole files run at 3.0 s/MB against 2a's dense list at 6.5–7.5:
comments, blank lines and short declarations are cheap. That is the top
of §5's 2.5–3.5 s/MB for the whole formatter before any pass or printing,
so SW-3837 (speed) has work to do; nothing was changed for speed here,
and so nothing was profiled.

### Friction

- **A row-polymorphic traversal didn't check.** With the steps' abilities
  a row variable (`onExpr: Expr → {e} Expr`, as `List.any` has), the
  mutually recursive functions were refused with E-NOT-A-FUNCTION ("this
  isn't a function: it's applied to an argument") at a call from one to
  another as a `let`'s value, and with E-ABILITY ("its row variable isn't
  part of the enclosing function's abilities") inside a `match` that is a
  `let`'s value. Fixing the ability to `Fail` cured the first; the second
  stayed for `Fail` too, so each optional part has a helper function
  (`traverseOptional`, `traverseAfter`). About 15 minutes.
- **Keywords as names, again**: `type`, `interface`, `export`, `opaque`,
  `forall`, `decreasing`, `unfolding`, `namespace`, `instance` can't be
  fields or variables, so `isInterface`, `exportKeyword`,
  `decreasingClause`, `hasNamespace`.
- **A lambda calling a recursive function isn't seen as a smaller call**:
  `let ex := (inner: Expr) => inner.traverse …` failed termination.
- **A record pattern can't follow a constructor in a pattern**
  (`Effect { open, … } result`: "braces after `Effect` take no further
  arguments"): bind the record, then match it.
- **The native build takes 1 min 50 s** and makes a 300 MB executable, so
  each round of the gate costs two minutes before it starts.

### Left for 2c

- Blocks of several lines, a block's `let` and local definitions (and with
  them `decreasing` and `unfolding` placing `:=` on a line of its own,
  `allow` in a block), `handle`, `calc`, `rewrite` (and `rules` sets),
  `cases`, `match induct`/`reify`, each a `notYet`.
- The fixed tokens of stage 2a's expressions as `Comments`.
- `lambda_result_type`'s error (a lambda written `(x: A): B => …`) is not
  ported; such a file gets another first line.
- Mismatched brackets: the Rust parser pairs brackets by a stack that
  ignores their kind, and so does `skipGroup`, but its lambda lookahead
  reads one case differently (the gate's one difference).

## Stage 2c (SW-3847): blocks, `let` and the proof steps

Opus, 17 November 2026.

### What is here

| File | What | Rust counterpart |
|---|---|---|
| `Syntax/Statements.sw` | a block's statements (`let`, local definitions), the expression `let`, `handle`, `match induct`/`reify`, `calc`, `rewrite` (rules, `repeatedly` sets, `at`, `then`), `cases`, `then_body` | `statement`, `let_statement`, `local_def`, `handle`, `handler_clause`, `induct_expr`, `reify_expr`, `calc_body`, `rewrite_body`, `cases_expr`, `then_body` |
| `Syntax/Parser.sw` | `block` reads every line (no more "not parsed yet"); `Modes` gains the ends that look back; R1's gaps and what comes first after them; `skipGroup` pairs brackets by kind; `lambda_result_type_ahead` | `block`, `is_stop`, `ends_construct`, `ran_out`, `match_brackets` |
| `Syntax/DeclParser.sw` | `definitionParts`, shared by top-level and local definitions, threading the expression parser's `self`; `:=` on its own line after `decreasing`/`unfolding`; `rules` declarations | `definition`, `rule_set` |
| `Syntax/Expr.sw`, `Decl.sw` | `Block`, `LetIn`, `Handle`, `Reify`, `Induct`, `Calc`, `Rewrite`, `Cases`, `Statement`, `Let`, `HandlerClause`, `InductArm`, `CalcStep`, `RewriteRule`, `Rules`, `RuleSet`, `RuleSetDecl`, and their dump | `NodeKind`s of the same names |
| `Syntax/Traverse.sw`, `Lowering.sw` | the new nodes traversed; a local definition's parameters checked for repeats | |
| `Syntax.Tests.Statements` | 19 tests, one or more per construct | |

`notYet` is gone: nothing is refused for being unported.

### The block, and why read-back can be proved

A block is `Block (first: Statement) (rest: List Statement) (result:
Expr)`: its lines before the value, then the value, each a node, with no
column, no line start and no count of lines. A block of one line is that
line's expression, so a `Block` always has a statement (the type says
so). The same holds for the other layout constructs: a `calc` is its
steps, a handler its clauses, an `induct` its arms, each a list; none
keeps where it started.

The parser reads columns from the items (the block's column is the
column of the line `expr` saw start right of the enclosing one, as in
Rust) and drops them when it builds the node; every column decision is a
function of the items, never of the tree. So the read-back statement for
S3 has the printer on one side: the printer puts each line of a `Block`
at one indent deeper than the line the block hangs from, and reading
back needs only that (1) each line starts a line at that indent, (2)
nothing inside a line starts a line at or left of it (the printer's
continuation indent is deeper), and (3) the line after the block is
shallower or is `|`, `where`, `:=`, `decreasing` or `unfolding`
(`endsBlocks`). Each is a fact about the printer's indentation per
construct, stated over the tree's structure; none needs the tree to
remember a column [the shape of the argument; nothing is proved yet]. That is SKETCH.md's risk 3 split into per-construct
lemmas of one shape: "printed at indent `i`, every line of the node
starts right of `i`, and its first at `i`", with `stopsByLine` and
`endsConstruct` the only places the parser looks at columns.

Two things make the proof easier than the Rust code suggests:

- The looks back of `is_stop` (a `rewrite` rule's `then`, a `let`
  value's `;`, a guard's `=>`) are bracket depths, not token indices:
  `Item.depth` minus the depth at the rule's first item is Rust's
  `bracket_depth(start, i)`. The printer keeps brackets, so the depth is
  the same in its output.
- A `calc` step ends at a line starting with `_` whatever the brackets
  (`inCalc`), so the printer must never start a line with `_` inside an
  operand: one more obligation of the same shape, on the printer [not
  checked against the Rust printer yet].

### R1 gaps

A recovering body that runs out (R1) is reported and the Rust parser
reads on; its errors are sorted by position. The twin stops at the gap,
so it has to know which error the Rust side sorts first: the gap, unless
a block then ends on a `let` or a local definition (reported at that
line's first token, before the gap), or a local definition's result type
ran out (no body, reported at its keyword). `Modes.lines` is the stack
of blocks being read, innermost first, with what each block's current
line is; an expression that a token must follow (an `if`'s condition, a
scrutinee, a `let`'s type, an expression `let`, a guard) is read with
the stack empty (`Modes.sealed`), since a missing token there is an
error after the gap. Found by the broken copies below: 3 of 1,600
differed before this.

### The gate [measured, Speedwell, load 4 to 8]

| Input | Stage | Identical | Not parsed yet | Other differences |
|---|---|---|---|---|
| `goldens` (124) | tree, refusal | 124, 124 | 0 | 0 |
| `repo --sample 300` | tree, refusal | 300, 300 | 0 | 0 |
| `fuzz --fuzz-cases 300` (235 lex) | tree, refusal | 235, 235 | 0 | 0 |
| broken copies of repo files using 2c constructs (cut, a token deleted, swapped or inserted, a line dedented near `let`, `rewrite`, `calc`, `handle`…), three seeds | refusal | 400, 600, 600 | 0 | 0 |
| hand cases: every 2c error, gaps in each position, `then` ending its line, `(f x).at`, nested `rewrite`, the mismatched bracket | refusal | 92 | 0 | 0 |

The mismatched-bracket case (`[a: (x: Type] a) => x`) is right now:
`match_brackets` pairs by kind and passes over a closer that doesn't
match the innermost opener, which 2b's note had the other way round;
`skipGroup` and `groupInside` do the same. `(x: A): B => x` gets
`lambda_result_type`'s error. `f !!b` (SW-3853) is refused by both: the
Rust side reads it as `f` and then a stray `!` ("expected the end of the
declaration, but found `!`"), and so does the twin; K4's note that Rust
reads it as `f (!(!b))` doesn't hold for this binary.

The broken-copy generator and the hand cases are scratch (no repo
bloat), as 2a's and 2b's were.

### Speed [measured, Speedwell, load 4 to 6]

400 repo files sampled at random (seed 7), 2.18 MB, one process,
`--batch`, two runs each:

| Stage | Time | Per MB | Peak memory |
|---|---|---|---|
| `tokens` | 3.9–4.0 s | 1.8 s/MB | 77 MB |
| `tree` | 6.9–7.1 s | 3.2 s/MB | 88 MB |

2b measured 1.7 and 3.0 s/MB on its 972-file subset, so parsing and the
dump went from 1.3 to 1.4 s/MB: within noise and the sample's mix (the
files 2b couldn't read are the proof-heavy ones). Nothing changed for
speed; SW-3837 has the profile.

### Friction

- **Keywords as names, a third time**: `calc`, `handle`, `rewrite` and
  `cases` can't be function names or fields (`calcExpr`, `inCalc`).
- **A method call on a record update doesn't run its effect**: `match {
  modes | allow = Some before }.peek with` was refused with "these
  patterns match an `Option`, but the argument has type `{Parse Item}
  Option Tok`"; binding the record first works. The message didn't say
  the call was the problem.
- **No effects in a guard**, again (`| Succ more if modes.at Comma`):
  bind first.
- **Field projection of a record argument blocks termination**:
  `header.decreasingClause` in `Header.lines` made the mutual recursion
  through local definitions fail; destructuring the record fixed it, as
  2a found for `fields.fields`.
- **The Rust R1 recovery is the hard part to mirror**, not the grammar:
  the parser reads on after a gap and sorts its errors, so the strict
  twin needs a model of which later error lands earlier (above).

### Left

- The tree stage for files that don't parse (an `Error` node holding
  what parsed): status 1 stays, as the brief says.
- Local definitions' parameters are checked for repeats after the
  block's other lowering checks; Rust checks the header first. They
  differ only for a file with both errors.
- A gap in a local definition's result type that is an equation (`def g:
  a =` with nothing after) is E-DEF-EQUALS in Rust and "needs a body"
  here; not seen in any input.
- Stage 2a's expressions still hold every token as a `Word`; the new
  nodes hold fixed tokens as `Comments`.

## Stage 4a (SW-3863): the four tidy passes

Sonnet, 17 November 2026.

### What is here

| Piece | Where |
|---|---|
| The passes P1 to P4, each a `SourceFile → SourceFile` made of steps given to the traversal | `src/Fmt/Passes.sw` |
| The traversal's steps as a record: `Steps` (`expr`, `pattern`, `header`, `decl`, `fields`, `attributes`, `ruleSet`), `Steps.keep` for the identity; the lowering's checks became `checkSteps` | `src/Syntax/Traverse.sw`, `Lowering.sw` |
| `Group.bare`: no comment on a header group's tokens but above its opening bracket, set by the parser, which P4 reads so it needn't walk a type for comments | `Decl.sw`, `DeclParser.sw` |
| The parked comma: `Lexed.settledBare` (the last commas out, then rule N) and `Lexed.tidied` | `Settle.sw`, `Passes.sw` |
| `Fmt.Twin --stage passes` (and `tidied`, the last tree only, for timing) | `Fmt/Twin.sw` |
| The Rust side: `stitchwort dev passes FILE` (`passes::dump_after_each`), and `dev/fmt-twin passes` | `crates/fmt/src/passes.rs`, `crates/cli`, `dev/fmt-twin` |
| Tests | `src/Fmt/Tests/Passes.sw` (13), `the_dump_after_each_pass_shows_the_tree_that_pass_left` |

### The passes' shape

- **P1** is a `header` step (a theorem with an explicit `(` group and no `∀` gets one). It is also applied to local definitions, as `each_node` does.
- **P2** is `expr`, `pattern`, `fields`, `attributes` and `ruleSet` steps that clear the trailing-comma flag. A one-item tuple can't exist (`(a,)` is a parse error), so no pass has to turn one into a bracketed item.
- **P3** is an `expr` step on `Effect` (the brackets at the left end of a row's result) and a `decl` step on a top-level definition (the brackets around a binder's whole type, found down the spine of the header's type and not inside brackets). The Rust pass asks the parser whether a candidate still reads as the same declaration; here the answer is the grammar's ladder: `Expr.level` says how tightly an expression binds at its top and `leftNeeds` how tightly an operator needs its left side to bind, read off the Rust pass's answers (a matrix of 24 expressions against 16 operator positions) and `Syntax/Parser.sw`. Three cases are special in the Rust answers: a negative numeral (`{Fail} (-1)` stays), a `!` before `∈`, and a row that reads as a record (`rowReadsAsRecord`: `{e}`, `{e, f}`, `{}`, `{E.e}`: first ability lowercase-led) keeps the bracket of anything `startsApart` (a section, a prefix operator, `match`, `if`, `include`…; SW-3876).
- **P4** is a `header` step (kinds `def` and `theorem` only; an `instance` isn't merged) and an `expr` step on `∀` and lambda (not `∃`).

Each pass is `file.apply steps`: the declarations traversed one by one under `Fail.toResult`, since the traversal's steps have the ability `Fail` (a step can't have a row variable there, see stage 2b's friction) and a tidy step never fails. Nothing is `Partial`.

### The parked comma

Rule N parks a comma's comments on the next token; the Rust P2 then deletes the comma from the text and rule N runs again, which gives a different answer when the comma starts its line and has a comment above (proof plan §10, K1). `Lexed.settledBare` is the sketch's `withoutLastCommas` on the real leaves, and `Lexed.tidied` parses it for P2 on when `parksComment` finds a comma before a closer holding a comment as the lexer left it. The tree dump leaves comments out, so the harness can't see this family at all; `the parked comma` test compares `settledBare`'s token dump with rule N's on the text with the comma written as a space, for the K1 case. Where no comma parks a comment (nearly every file) P2 is the tree step on the one parse.

### The gate [measured, Speedwell, load 5 to 9]

| Input | Identical |
|---|---|
| `goldens` | 124 of 124 |
| `repo`, `--sample 300` | 300 of 300 |
| `repo`, `--sample 400 --sample-seed 9` | 399 of 400 (the one is a stage 2 difference: `"""…""".lines`, below) |
| `fuzz`, `--fuzz-cases 300` | 253 of 253 |
| `fuzz`, 300 cases, comment rate 0.2 (seed 7) and 0.3 (seed 11) | 228 of 228; 216 of 216 |
| `disturbed` | 61 of 62 (the one is a stage 2 refusal message, below) |
| 739 hand-written cases (scratch): the row table (34 expressions against 19 operator positions, alone and doubled in brackets), binder types, merges and what keeps them apart, every comma bracket, local definitions, comments in brackets | 739 of 739 |

The first differences fixed on the way, all in P3's table: a negative numeral's brackets (`{Fail} (-1) → z` stays), a `!` before `∈`, and a constructor with fields (`C { x = 1 }`) which stands bare as a function head. Everything else agreed on the first run, which is the table's doing: it was read off a matrix of the Rust pass's answers before the code was written.

Found in the stage 2 parser, not fixed here:

- `"""…""".lines` (a multi-line text, then a method) reads as an application of the text to a section, not a field access: `aoc/src/Aoc/Year2024/Day06/Tests/Examples.sw`. A `--stage tree` difference.
- `disturbed`'s `00057-sequence-semicolon-comment.after.sw`: Rust says "expected an expression, but the line ends here", the Twin "a block must end with an expression, not `let`" (a `--stage refusal` difference).

### Speed [measured, Speedwell, load about 8]

107 files of `aoc/src`, `std` and `tools`, 0.87 MB, one process, `--batch`: `--stage tree` 2.80 s user; `--stage tidied` (parse, the four passes and one dump) 3.03 s user. So **the four passes cost about 0.25 s/MB** (0.23 s for the 107 files), on top of 3.2 s/MB for lexing, parsing and a dump. Peak memory 78 MB (75 MB for `tree`). The harness's whole-run numbers on 300 sampled files (about 1.07 MB), jobs 1: `tree` 6.5 s, `passes` (four dumps) 8.6 s at load 9.

### What 4b and 5 inherit

- `Steps` and `SourceFile.apply`: `meaning` and the passes' proofs are statements about one traversal with these steps. The generic lemma is about `traverse`, the step facts are each step's shape (P1 a header step; P2 five steps that clear a flag; P3 `dropAfterRow` and `dropDeclBinders`; P4 `mergeHeader` and `mergeBinding`).
- P3's side condition is a function, `dropLeft`, with `Expr.level` and `leftNeeds`; it is a statement to prove (a dropped bracket pair reads back as the same tree) against the parser, not a trial parse. The table is the thing to review.
- `Group.bare` is parse-time information, and `Lexed.tidied` reads leaves before the parse: a proof that P4 leaves comments alone uses `bare`'s definition, not the tree.
- A printer should expect no trailing comma, no theorem with explicit parameters lacking `∀`, no mergeable adjacent groups, and no spare bracket after a row or around a binder's whole type: the tree `Lexed.tidied` gives is tidy for all four.

### Friction

- **`task`/harness: every `dev/fmt-twin` run rebuilds the native executable** (1 min 50 s) unless `--exe` is given, so five gate runs cost ten minutes; the wrapper script of SW-3847 or `target/fmt-twin/fmt` with `--exe` avoids it.
- **A row variable in a step's ability still doesn't check** (as in 2b), so every step is `{Fail}` and each declaration goes through `Fail.toResult` with a fallback that never runs.
- **`stitchwort check` of the project takes 13 to 31 s** with every edit; the Traverse change (one parameter to a record) touched 40 functions and was one script, which is the cost of not having the row variable.
- **Brackets in expressions are inconsistent in the dump**: `Paren` has its own node, `(a, b)` is `Tuple`, `(x: T)` is `Annotation`, and the Rust pass can't tell them apart by tokens (it asks the parser); the table in P3 had to say which node kinds hold a bracket pair.

## Stage 4b (SW-3864): `meaning`

Opus, 17 November 2026.

### What is here

| Piece | Where |
|---|---|
| `meaning`, the trusted definition of "the same program" (D3678's narrow form): the shared traversal with steps that forget what a pass changes, where it changes it; its doc gives the compiler's reading behind each thing it forgets | `src/Fmt/Meaning.sw` |
| The passes' step facts against it, proved: P2's five steps, P1's header step, P3's row step (`dropLeftForgotten`, by induction along the left end) and P3's binder-type layers (`stripUnwrapped`, `groupStripUnwrapped`, `paramStripUnwrapped`), with `levelAtomic` and `negativeKept` tying P3's table to `meaning`'s two exceptions | `src/Fmt/MeaningProofs.sw` |
| Tests: what it forgets, what it keeps (`(f) x` against `f x`, `{IO} (f a) b`, `{Fail} (a + b) * c`, a pair holding a comment, a dependent group, an `∃` group, `∀` on an implicit-only theorem), and `tidy` keeping it | `src/Fmt/Tests/Meaning.sw` (7) |
| `Fmt.Twin --stage meaning`: `kept`, or where `tidy` or `Lexed.tidied` change the file's meaning as its dump shows it (no Rust side) | `src/Fmt/Twin.sw` |

The steps P1, P2 and P3's row step became pure functions (`Expr → Expr`, `Header → Header`), which `Steps`' `{Fail}` fields accept, so that the facts are equations.

### The node kinds

All 98 of the Rust `NodeKind`s, as the real tree holds them:

| Kinds | Count | In `meaning` |
|---|---|---|
| `Paren` | 1 | forgotten at a row's result's left end (through `Binary` and its kin's left operand, `Chain`'s first, `App`'s head, `FieldAccess`'s target) and as a binder's or annotation's whole type; at an application's head only around an atomic form; never around a negative numeral |
| `Param`, `Binder`, `LambdaParam` | 3 | a header's (not an instance's), `∀`'s or lambda's group split one a name where P4 could have merged it; an `∃`'s and a function type's binder kept whole; the whole type unwrapped as above |
| `Theorem` | 1 | `∀` absent (SW-3882; was: where P1 writes it) |
| `Tuple`, `List`, `Record`, `PatternTuple`, `PatternList`, `PatternRecord`, `PatternCtorFields`, `Fields`, `Attributes`, `RewriteRules` | 10 | the comma flag `False` (`Import` has none in the tree: the parser keeps no flag for it) |
| `Effect`, `Annotation`, `FunctionType`, `Forall`, `Exists`, `Lambda`, `PatternTyped` | 7 | where the rows above apply; otherwise kept |
| every other kind but `Error` and `Expression` | 74 | kept: the traversal goes into its parts and the step is the identity |
| `Error`, `Expression` | 2 | never in a file's tree (the parser is strict; a lone expression isn't a file) |

### Checked [measured, Speedwell]

- `tidy` and `Lexed.tidied` keep `meaning`'s dump on the 124 golden files and on 223 repo files (every fourth `.sw` under `crates/elab/src/std`, `aoc/src`, `tools` and `games`, 2.4 MB, 15.5 s, 168 MB peak).
- `dev/fmt-twin passes --inputs goldens`: 124 of 124 identical.

### What 5 inherits

- **Comments are in `meaning`** (it keeps every `Word` with its comments). *Superseded by SW-3882, below.* The parked comma (K1) moves a comment when P2's comma goes, so `Lexed.tidied`'s tree can differ from the parse in where a comment sits, and the top theorem's `after.meaning = before.meaning` can't hold there as stated [inferred: the dump the checks compare leaves comments out, so they can't see it]. Either `meaning` leaves comments out and `tidyKeepsComments` carries them, or the top theorem is stated with K1's case apart.
- **The generic lemma.** P1's and P2's steps change a flag or keyword at the node, so the plain lemma (a traversal whose step keeps the meaning step keeps `meaning`) finishes them. P3's steps rebuild descendants, so it needs the stronger form: `meaning`'s traversal commutes with `dropLeft` and `dropDeclBinders`. P4 needs `splitGroups (mergeGroups gs) = splitGroups gs` for plain groups, which rests on `Group.typeLines` telling types apart when they hold no comment.

### After the review (SW-3878 → SW-3881, SW-3882)

The review is `docs/reviews/SW-3878-meaning.md`. SW-3881 fixed M2 (a constructor update with a base is an application). SW-3882, Opus, 17 November 2026:

- **Comments are left out** (the orchestrator's call under D3678; the review found nothing `check` or `run` reads but a `--|` doc's links). No step reads a comment: the `bare` conditions in `unwrapped`, `forgetLeft` and `Group.splits`, and `noComments` in `Group.pieces`, are gone, so `meaning` now forgets a pair or splits a group that holds a comment. Meanings are compared with every comment blanked. The value still holds each `Word`'s comments and `Group.bare` (the tree has no comment-free form, and blanking them is a map over about 90 token sites); the checks compare the dump, which prints neither. For stage 5's top theorem that means stating it on the dump or adding that map; until then "equal meanings" means "equal once comments are blanked", and a split group's pieces each keep its `open`.
- **`∀` is absent on every header** (`plainForall` is gone): the parser allows it on theorems only and the lowering skips it.
- **The doc's grounds** now say what is left out on purpose (positions, comments), cite the lowering's test on an application's head (its first token is `(` and it lowers to an application), and cite D3679 for the group split (SW-3880 makes the elaborator check a group's type once per name).
- **`CommentsKept`** (in `Meaning.sw`, a `def` of the `Prop`; the theorem waits for the printer): between the source's leaves after `settledBare` (rule N with P2's commas out, so K1's moves are in it) and the output's after rule N, (1) `commentViews` equal: every comment's text, own-line or trailing, blank line above, in order, the file's end included; (2) `holders` equal: the comment-holding tokens in order with their text, count above, trailing or not, and (3) whether a blank line separates the comments above a token from it. (3) is stated for every token, more than docs need; narrow it to declaration and member first tokens if the printer can't keep it inside expressions.
- Statements: none in `MeaningProofs.sw` changed, and every proof checks unchanged (P3's `drops` still carries `dropLeft`'s own `bare` test; `forgetLeft` no longer asks for it). Tests: "a pair holding a comment" and "`∀` on an implicit-only theorem" now have the same meaning; a new test leaves comments out of a row pair, a group and a binder type.
- Checked: `dev/fmt-twin passes --inputs goldens` 128 of 128 identical; `Fmt.Twin --stage meaning` `kept` on all 128 golden files [run].

### The oracle for `meaning` (SW-3883)

`Fmt.Twin --stage meaning` only checks that `tidy` keeps `meaning`; it can't catch a `meaning` that equates two programs the compiler tells apart (review S4). `dev/fmt-meaning-oracle` asks the compiler:

- **How**: for each pair of files, `Fmt.Twin --stage meaningdump` prints `meaning`'s dump (run from this worktree's sources with `stitchwort run Fmt.Twin.main`, so a change to `Meaning.sw` is tested without rebuilding the Twin; the first run in a fresh worktree checks the project, about 20 s). The pair is *agreed* when the two dumps are equal. Each side's files then go to the compiler as namespaces of one project, `stitchwort hash --json` (a declaration's hash, its type's hash, its kind), and the oracle compares the two sides: the same hashes, or, for a file that doesn't check, the same diagnostic codes. An agreed pair that differs is a finding, and the exit status is 1.
- **Pairs** (118): the 64 golden before/after pairs; groups, `(x y: T)` against `(x: T) (y: T)` in a `∀`, `∃`, theorem header, def header and lambda, for `T` in `_`, `Box` (`def Box [t: Type]: Type := List t`), `Nat`, `List Nat`, `Bool`, with the review's probe bodies for `_` and `Box`; and 14 bracket cases at the head of an application, at the left end of a row's result (where P3 and `meaning` forget a pair) and outside one, round atoms, applications, a constructor update and a constructor with fields. A head case carries whether `meaning` should forget the bracket; a mismatch is a note.
- **Expected differences**: a probe group in a `∀`, theorem or def header is expected to differ until SW-3880 (D3679). The binary it ran against already reads groups as sugar, so those six agree and are listed as "now agrees"; the expectation can go once SW-3880 is merged.
- Run: `nice -n 19 dev/fmt-meaning-oracle [-v] [--keep DIR] [--cache-dir DIR]`, about 35 s cold (25 s of it the compiler reading the library once; `--cache-dir` keeps that between runs, then about 7 s). The compiler is `target/release/stitchwort` of the main checkout (`--stitchwort`, or `STITCHWORT_MAIN_CHECKOUT`).
- **Checked**: it flags a regression. With `Meaning.sw`'s `CtorFields _ (Record _ (Some _) _ _ _) => False` line deleted (SW-3881 undone), `(Pick { r0 | x = 1 }) 2` and `Pick { r0 | x = 1 } 2` are agreed and the oracle reports E-DEFAULT-POSITIONAL on the second, exit 1.
- **Today**: 101 pairs agreed, all 101 the same to the compiler (49 hash-identical, 52 failing alike: most goldens are formatter fragments that don't check), 17 told apart by `meaning` (the `∃` groups, which it deliberately keeps whole; the bracket cases that are kept; a golden with an `import`, which the Twin refuses; comments and text blocks), 0 findings.
- Limits: the golden pairs mostly fail to check, so the compiler's answer there is its diagnostic codes only; the generated pairs are the ones that exercise hashes.

### P3's table against the parser

Read against `Syntax/Parser.sw`'s ladder (`operatorExpr` → `logicChain` → `cmpExpr` → `pipedRange` → `rangeExpr` → `appendExpr` → `addExpr` → `mulExpr` → `unary` → `app` → `atom`), `Expr.level` and `leftNeeds` agree rung for rung: each operator's left operand is parsed one rung up, or at its own rung where it nests to the left (`+`, `*`, `|>`), and `↔`'s 3 is the same as 4 since no level is 3. 30 probes after `{Fail}` (sections, `match`, `if`, `include`, a prefix before `*` and `∧`, constructors with fields under a field access, chains, ranges, pipes, `↔`) are identical to Rust.

It is wrong after a row that is a lone row variable, `{e}`: there the bare form reads as a record, `{e}`, applied to what follows, so Rust keeps the pair and the Twin drops it. `{e} (.f)`, `{e} (match x with | _ => 1)`, `{e} (include "x") y`, `{e} (-x) * y`, `{e} (!x) ∧ y` and `{e} (if a then b else c)`: 0 of 6 identical [run]. `meaning` is unaffected (the trees differ only by the `Paren`); the Twin's P3 output there doesn't print back to its own tree.

Provable as written? The table's facts, given `Parsed` stated by the same ladder, are an induction along the left end like `dropLeftForgotten`; but "a dropped pair reads back as the same tree" is not a fact about the table alone: it needs the row's form (`{e}` above) and the token rules for a `-` or `!` after `}` (`argument_prefix`), which the table models only as `keepsBrackets`. So not as written: with the row-variable case fixed it is provable as part of `printParses`, not on its own.

### Friction

- `cases` splits a record's every field as a fallback and runs out of its 64 cases on `Header` (11 fields) though the goal turns on three; splitting the record by hand, then `kind` and `forallKeyword`, then matching the `any` closed it by computing.
- `cases then [lemma inner]` doesn't see `inner` refined by the cases it makes; a `let` of the lemma before `cases` does.
