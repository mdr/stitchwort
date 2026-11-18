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

## The traversal lemma and P1 to P3 (SW-3877)

Opus, 17 November 2026.

### What is here

| Piece | Where |
|---|---|
| `walk`, a pure copy of the traversal arm for arm, with `Pure` steps; `Agrees on p` (each of `on`'s steps finishes with `p`'s result) and `Keeps s m` (each of `s`'s steps keeps what walking with `m` gives of the whole node it rewrites) | `src/Fmt/Walk.sw` |
| `…Ok` (39): with agreeing steps the traversal finishes with the walk's result; `…Twice` (39): walking with `s` then `m` is walking with `m`; `applyKeeps`: `(file.apply on).apply mean = file.apply mean` | `src/Fmt/Walk.sw` |
| P1, P2 and P3 keep `meaning` file by file (`forallKeepsFile`, `commaKeepsFile`, `bracketKeepsFile`) and the three in order (`firstThreeKeepMeaning`); P3's facts through the walk: `dropLeftWalk` (with `negativeWalk`, `atomicWalk`), `spineWalk`, `stripWalk`, `groupBindersWalk`, `paramsBindersWalk`, `headerBindersWalk` | `src/Fmt/MeaningProofs.sw` |

No axioms (`stitchwort axioms Fmt.Proofs.firstThreeKeepMeaning`).

### How

- `Keeps` is the strong form: its condition walks the whole rewritten node with `m`, so a step that rebuilds descendants (P3's) is covered, and the proof of `…Twice` is congruence alone. No weak form was needed: P1's and P2's conditions close by computing.
- The traversal's arms elaborate to binds of the children's computations, then a pure constructor, then the step. `Std.Fail.toResultThen` with a finished child (`seqN`, `seqNk`; `seqNj` for the record-matching functions, where the step is applied in the arm's own `let`s) turns an arm into its pure copy in one call. The 78 family proofs were generated by a script from a table of the arms (each arm's constructor and which children it traverses); two fixes to the script and they checked.
- P3 after a row: `dropLeftForgotten`'s induction again, but `forgetLeft` now sees the walked inner form, so the walk must keep `negativeNumeral` and `atomic`. Around a binder's type: `unwrapped` of the walked type, for every binder `spineBinders` reaches.

### P4 doesn't keep `meaning` as stated

`Group.pieces` gives each piece the group's `open` (`Comments`). After P4, `(x y: T)` has the first group's `open`; split by `meaning`, both pieces carry it. So `-- note` above `(x: Nat) (y: Nat)` is on `x` only before P4 and on both after: the meanings differ as values (checked with a scratch test: the pieces' `open.above` lengths are `[1, 0]` before, `[1, 1]` after). The dump leaves comments out, so the checks never saw it. To prove P4 it needs, besides comments blanked in the comparison:

- annotations equal from equal `typeLines`: the dump of a comment-free type telling types apart (an induction over `Expr.lines`), or `joins` comparing blanked trees;
- equal `kind`s: `joins` doesn't compare `GroupKind` (the parser never mixes them in one list, but nothing in the tree says so);
- `Group.bare` is parse-time and not tied to the tree's comments, so a proof can't use it; with comments blanked it doesn't need to.

## Engine stage E1 (SW-3905): the engine harness

`stitchwort dev doc FILE` writes, per declaration, `decl N`, `size K` (nodes written out in full), `text ESCAPED` (Rust's printed text) and the layout document one node a line in pre-order (tag, arguments, children after; `Shared ID`/`Ref ID` for shared docs). `dev/fmt-twin engine` caches the dumps, runs `Fmt.Twin --stage engine` over them (`Fmt.DocDump`: reads a `Fmt.Doc`, prints in 120 columns, compares) and counts matched, mismatched, unsupported (by node kind) and oversized (over 50,000 nodes written out in full: `Doc.size` and `forcesBreak` walk a shared doc once per use, so E2 needs them cached first).

Baseline (before E2): goldens, 644 declarations: 22 matched, 0 mismatched, 622 unsupported. Repo, 34,531: 4,303 matched, 0 mismatched, 29,838 unsupported, 390 oversized. `IdGroup`+`IfBroken` (every declaration body) is 25,442 of the unsupported alone.

## Engine stage E2, part 1 (SW-3921): `IdGroup` and `IfBroken`

`Doc` has `IdGroup id inner hard` (a group whose decision the printer records) and `IfBroken id broken flat` (the branch by the recorded decision; flat when the group hasn't printed). The printer keeps `modes: List (Nat, Mode)`, the latest first, as Rust's `BTreeMap` insert overwrites; `fitsFrom` takes `modes` too. As in Rust, a broken `Fill`'s first item and a `OneLineBelow` option are measured with no modes recorded, so an `IfBroken` there measures its flat branch even after its group broke: Rust's `fits_flat` passes an empty map. That is a measure that can disagree with the printer, of the D1–D4 kind; no harness declaration meets it.

Proofs: every theorem keeps its statement, none restricted. Readings give `IdGroup` the `Group` step plus the record; `IfBroken` is the printer's own step. `Words`' `Uniform` asks both branches to have the same words; `Marked`, `Joins`, `Lays` and `Puts` ask it of both branches; 9 new lemmas (`pickEither` and one per layer). `audit Fmt.Doc`: 319 theorems, 0 failed, 3 warnings (the known 4 less `spacesAfterComment`, which the random search now meets).

Harness [measured, Speedwell, load about 8]: goldens, 644 declarations: 548 matched, 10 mismatched, 86 unsupported (were 22, 0, 622). Repo, 34,753: 32,085 matched, 0 mismatched, 2,278 unsupported, 390 oversized (were 4,303, 0, 29,838 of 34,531). The 10 golden mismatches are toy-versus-Rust differences of the plan's §1.1, not this port: 4 are the flat `SoftLine`/`Line` while a comment waits (`g (a, b) -- c` and `{ x = 1, y = 2 } -- c` in `comment-on-the-last-item`, where the toy breaks), 6 the comment floor against `CommentEnd` (`comments-anywhere` declarations 7, 14, 17: the line after an own-line comment, Rust at the floor 2 or 4 deeper).

## Engine stage E2, part 2 (SW-3926, SW-3927): `NarrowGroup`, `Align`, `AlignInset`, `Displaced`

SW-3926: a broken `Fill`'s first item and a `OneLineBelow` option are now measured with the modes recorded, as Rust's are since SW-3913, so the D1–D4-kind disagreement part 1 describes is gone. The test is SW-3913's (`an IfBroken in a one-line-below option sees an earlier group's mode`); it fails with the empty record.

SW-3927: `NarrowGroup max inner hard` is a `Group` measured in `min left (max - column)`; `Align` indents its contents' breaks to the column it starts at (`indent` at a line start), `AlignInset` likewise (`indent + 2` at a line start); `Displaced` ends a waiting comment's line first (`Printer.displace`: `lineStart` when a comment waits) and indents its contents to where its first line lands (`Printer.displacedAt`: the owed indentation if deeper at a line start, the construct's after words, the comment break's after a comment). `fitsFrom` measures all four as Rust's `fits_in` does: the narrow group as a group, the other three as their contents at the same indentation. DocDump reads all four; `missing` is gone (only `Mark`, `CloserLine` and `TextBlock` are still unsupported, read as empty).

Proofs: every theorem keeps its statement, none restricted. Readings give `NarrowGroup` the `Group` step; the other three are the printer's own steps. `Joins`: `Align`/`AlignInset` are their contents; `Displaced` asks its contents from the edge as it is and, where a comment waits, from a fresh line too (`DisplacedJoins`, as `StartJoins`). `Puts` and `Lays`: `AlignHolds` asks the contents at `atStart` at a line start and at every column after words, since a place doesn't track the column; `DisplacedHolds` gives the contents the indentation and start place the printer does (a comment break from `Held`). Words, `Uniform`, `Marked`: the contents'. New lemmas: `alignAtStart`, `alignHere`, `displaceClear`, `displaceWaiting`, `displacedAtStart`, `displacedAtMid`, `displacedAtHeld`, `displacedStays` (Places), `displaceHolds` (Joins), `displaceWords`, `displaceQuiet` (Words). `displacedAt` uses `owed.getOrElse 0` where Rust has `owed.unwrap_or(indent)`: the same under `max indent`, and it matches `Agrees`' own form. `audit Fmt.Doc`: 330 theorems, 0 failed, the 3 known warnings (`closesWord`, `putMid`, `putSpaces`).

Harness [measured, Speedwell]: goldens, 644 declarations: 614 matched, 12 mismatched, 18 unsupported (were 548, 10, 86). Repo, 34,795: 34,207 matched, 0 mismatched, 198 unsupported (all `TextBlock`), 390 oversized (were 32,085, 0, 2,278, 390 of 34,753). The 12 golden mismatches are all E3's: the 10 of part 1, and `paren-comment-in-body` (before and after), `Both ( ) -- c` where Fmt.Doc prints `Both () -- c`: Rust holds the space after a waiting comment and writes it before the closer, Fmt.Doc drops it (held spaces). The 18 unsupported are `TextBlock` (12, E5) and `Mark`+`CloserLine` (6, E4).

## Engine stage E3 (SW-3932): comments as engine.rs prints them

The printer gains `heldSpaces` and `commentFloor`, and `CommentEnd` is gone:

- Spaces written while a comment waits are held, and written before a closer on the comment's line (`Printer.writeHeld`).
- Other code after a waiting comment starts a comment break (`commentBreak`: `newline (continuation indent)`).
- A flat `Line` is a written (or held) space, and a flat `SoftLine` nothing, whether or not a comment waits.
- `LineStart` after text breaks at `max indent (line + 2)` and sets the floor there. Every `newline` breaks at `max indent floor` and drops the held spaces. Writing a text that doesn't start `--` clears the floor (`floorAfter`), as `before_code` does.

`fitsFrom` measures as `fits_in` does. Its last argument is `Trailing` (`Clear`, or `Pending held flatBreak`): spaces after a comment add to `held`, a closer pays `held` with its own width, a flat `Line`/`SoftLine` after a comment sets `flatBreak`, and code after that doesn't fit.

Not ported: Rust's `before_code` at a line start, which writes code before a comment still waiting there. The toy keeps the comment first. `readingWords` (the printed words are the document's in order) would be false with Rust's order, and no rule builds such a document: `SuffixPuts` is `False` at a line start, so no golden or repo declaration meets it. `Printer.write`'s doc says so.

Proofs: every theorem keeps its meaning, none is restricted, and no goal is open.
- `Place`'s constructors carry the floor (`AtStart at floor` and so on) and `Agrees` asks the printer's `commentFloor` to be it.
- `Puts`/`Lays`: `HardLine`, `OneLineBelow` and the separators' broken arms go to `floored floor indent`, and `LineStart` after words starts a floor. `LineStartHere` is `HerePuts` (the floor kept, the break floored). `Held` now allows a flat separator (the space held) and a flat soft line.
- `Joins`: `SepJoins`/`SoftJoins` at `Waiting` ask both ways.
- Four theorems described the old printer and are restated to describe the new one: in Proofs, `lineAfterComment` (a flat `Line` holds a space), `softLineAfterComment` (nothing) and `spacesAfterComment` (held, not dropped); in Words, `closePut` (needs a waiting comment, and writes the held spaces first).
- New lemmas: `writeHeldWritten`, `commentBreakWords`, `floorWords`, `commentBreakQuiet` (Words); `gapAccepts`, `heldSound`, `heldPutOk`, `commentBreakHolds`, `floorHolds` (Joins); `floorAgrees`, `agreesFloor`, `heldAgrees`, `holdAgrees`, `sepStays`, `herePlace`, `hereBroken`, `startNotMid`, `commentBreakBreaks`, `herePutsWeaker` (Places); `hereLaysPuts` (Lays).
- `audit Fmt.Doc`: 351 theorems, 0 failed, 0 warnings.

Harness [measured, Speedwell]: goldens, 644 declarations: 626 matched, 0 mismatched, 18 unsupported (were 614, 12, 18). Repo, a 300-file sample, 5,773 declarations: 5,619 matched, 0 mismatched, 32 unsupported (`TextBlock`), 122 oversized. The native `Fmt.Twin` build peaks over 2 GB, so the counts come from a driver with only the engine stage (`Doc`, `Print`, `DocDump`).

## Engine stage E4 (SW-3940): closer marks

`Doc` has `Mark key` (notes the indentation of the line it is on) and `CloserLine key` (a line break for a closer that comments put on a line of its own: at the indentation in force, unless a line since the mark is at or left of that, then at the marked line's if less), as engine.rs prints and measures them: `CloserLine` forces a break and measures as `HardLine`, `Mark` as nothing. The printer's `commentFloor` became `carry: Carry`, the floor and the open marks (`OpenMark`: key, marked indentation, least indentation since, `None` before the next line break). Every `newline` lowers the open marks to the line it starts (`Carry.breakTo`); `CloserLine` closes its mark and the floor (`Carry.close`) before breaking at `Carry.closerAt`.

The rest of E4 was in place: E2 brought `IdGroup`/`IfBroken`, `NarrowGroup`, `Align` and `AlignInset` through every layer with no open goal. `Align`'s `AlignHolds` asks the contents at every column after words, since a place doesn't track the column; the plan's §3.2 had `Place` carry it. That spec is closed and sound, but the rules layer may find it too weak (a read-back at column 0 is not one it can prove); if so, the column goes into `Carry` the way the marks did.

Proofs: no theorem is restricted and no goal is open. `Place`'s second field is the `Carry` (it was the floor), so the marks ride along every place without a new field, and `Agrees` asks the printer's `carry` to be it. Line breaks in `Puts`/`Lays` go to `carry.breakTo indent`; a comment break before an own-line comment to `carry.startFloor broken`. `Mark` is `place.withCarry (place.carry.mark key place.indent)` in `Puts`, `Lays` and `Joins` (an edge it leaves as is); `CloserLine` is `CloserPuts`: after words, a line start at `place.carry.closerAt key indent` with the mark closed, and in `Joins` a line break. Restated to the new printer: `newlineBroken`, `newlineAgrees`, `newlineStays` (the marks see the new line), `lineStartBreaks` (the carry with its new floor), `floorAgrees`, `agreesFloor`, `floorHolds`, `floorWords` (a carry, not a floor), and `printPuts`/`printLays` start from `AtStart 0 Carry.none`. New lemmas: `carryAgrees`, `withCarryMid`, `withCarryCarry`, `markStays`, `closerStays` (Places), `carryTracks` (Lays). `audit Fmt.Doc`: 357 theorems, 0 failed, 0 warnings.

Harness [measured, Speedwell]: goldens, 644 declarations: 632 matched, 0 mismatched, 12 unsupported (all `TextBlock`; were 626, 0, 18). Repo, the same 300-file sample (seed 1), 5,792 declarations: 5,676 matched, 0 mismatched, 31 unsupported (`TextBlock`), 85 oversized. The engine-only driver (E3's `mkslim.sh`) builds in 320 MB.

## Engine stage E6 (SW-3944): `Fmt.Doc` is `Std.Doc`

Sonnet, 18 November 2026. The engine, its 357 theorems and its 35 tests moved from `tools/fmt/src/Doc/` to `crates/elab/src/std/Doc/` (`Doc.sw`, `Measure.sw`, `Print.sw` and the proof files); `Fmt.Doc` is gone and `Fmt.DocDump` imports `Std.Doc`. The older entries above say `Fmt.Doc`; read them as `Std.Doc`.

What a std file is: its names are written in full or imported, and a `namespace` line does nothing, so the type is `Std.Doc` itself (`Doc.text`, `Doc.group`), the printer's types and helpers are `Doc.print`, `Doc.Printer`, `Doc.Cmd`, `Doc.Carry`, `Doc.Mode`, and every proof and spec is `Doc.Proofs.X` (the tests' helpers `Doc.Tests.X`). A file brings the names in with `import Doc (..)` and `import Doc.Proofs (..)`.

Name clashes: the constructor `Empty` clashed with the type `Std.Empty` in other library files (a constructor's short name is in scope everywhere), so it is `Doc.Nothing`. `print` is the IO operation: the engine's is written `Doc.print`. `Reads` and `Pair` clash with prelude names (`Reads`, `Std.Pair`) and are written `Doc.Proofs.Reads` and `Doc.Proofs.Pair` where used.

The library loader's reference analysis ignored a file's imports, so a name imported and written short was not seen as a use of the file that declares it ("uses X, which isn't loaded"); `LibraryIndex::build` now applies each file's imports when it resolves the file's references.

Checked: `audit Std.Doc` 357 theorems, 0 failed, 0 warnings; `test --std Doc` 35 of 35; the harness on the goldens 632 matched, 0 mismatched, 12 unsupported (`TextBlock`), as before.

## A comment-free `meaning` (SW-3884)

Opus, 17 November 2026.

### What is here

| Piece | Where |
|---|---|
| The blanking map: one function a step (`blankExpr`, `blankPattern`, `blankHeader`, `blankDecl`, `blankFields`, `blankAttributes`, `blankRuleSet`), each blanking the comments the node holds itself and those of the records inside it with no step of their own (groups, rows, lets, arms, clauses, constructors); `blankSteps`, and `SourceFile.withoutComments` | `src/Fmt/Blank.sw` |
| `meaning`'s steps blank a node before they read it, and `meaning` blanks the file's end comments (`withoutEnd`) | `src/Fmt/Meaning.sw` |
| `meaningBlanksFirst`: `file.withoutComments.meaning = file.meaning`, through `applyKeeps` with `blankKeeps` (blanking a node keeps what `meaning`'s walk gives of it); 50 theorems, about one a blanking function | `src/Fmt/BlankProofs.sw` |
| `joins` compares the groups' `kind`s (SW-3908) | `src/Fmt/Passes.sw` |
| Test: a merged group's pieces hold no comments, before and after `tidy` (fails with the header step not blanking) | `src/Fmt/Tests/Meaning.sw` |

The decision was the plan's option (b) (`docs/proposals/self-hosted-fmt-engine-plan.md` §4): blank before the steps. It is done one node at a time, inside the one traversal, rather than as a traversal of its own followed by `meaning`'s: the passes' facts then stay `Keeps` facts about one walk, and `meaningBlanksFirst` is the plan's `file.withoutComments.apply meaningSteps`, so stage 5 gets equal meanings from equal blanked trees by congruence.

P1 to P3's proofs needed four changes: the binder-type lemmas are stated through the blanking (`(blankGroups …).map Group.plainType`), `parenWalkForgotten` takes any words for the pair (`meaning` sees the blanked ones), `negativeWalk` splits the atom's kind, and the file theorems apply to `file.withoutEnd`. No axioms (`firstThreeKeepMeaning`, `meaningBlanksFirst`).

### Checked [run]

- `Fmt.Twin --stage meaning`: `kept` on the 132 golden files and 224 repo files (every fourth `.sw` under `crates/elab/src/std`, `aoc/src`, `tools`, `games`), with a twin built from this branch.
- `dev/fmt-meaning-oracle`: 120 pairs, 103 agreed, all 103 the same to the compiler, 0 findings.
- `dev/fmt-twin passes`: goldens 132 of 132, repo `--sample 300` 300 of 300 identical (with `joins` comparing kinds).

### P4 and the four passes

`tidyKeepsMeaning`: `file.tidy.meaning = file.meaning`, no axioms (`src/Fmt/MergeProofs.sw`).

- **`joins` gained a second half** (the orchestrator's call): `joins = rustJoins ∧ meaningJoins`. `rustJoins` is the Rust pass's test as before, with `kind`s compared (SW-3908). `meaningJoins` asks that `meaning` read the two groups alike but for their names (`Group.meaningForm`, the group walked with `meaning`'s steps, blanked and unwrapped, compared with `Group`'s derived `==`), and that it split each of them and their merge (`Group.meaningSplits`: one group a name, so self-naming is asked of the walked type). The two tests read different trees: the dump compares raw tokens and can't be tied to the walked type in general (it leaves out an atom's `Tok`), and the walked comparison alone would merge `(x: Nat -- a) (y: Nat -- b)`, dropping a comment `meaning` can't see. Together P4 merges a subset of what Rust merges.
- **The proof**: `mergePieces` (two groups `meaning` reads alike, each split and split merged: the merge's pieces are theirs, by the names' lists), `joinedPieces` (what `joins` gives: `(a == b) = True` read as `a = b`), then induction along a header's groups (`mergeFromKeeps`) and a binder's parameters (`mergeParamsFromKeeps`, `mergeParamsKeeps`), and `applyKeeps`. `mergeHeader` and `mergeBinding` became pure, as P1 to P3's steps did in 4b.
- **Checked**, with the interpreted `Fmt.Twin` (`stitchwort run Fmt.Twin.main`; the native build peaks at 2.4 GB): `dev/fmt-twin passes` goldens 132 of 132, repo `--sample 300` 300 of 300 identical; `--stage meaning` `kept` on 132 goldens and 224 repo files.

## Slice 1, the program (SW-3950)

Opus, 18 November 2026. Proof plan ticket 12.

### What is here

| Piece | Where | Rust counterpart |
|---|---|---|
| The rules for `def name: T := e` and slice 1's eight constructs on `Std.Doc`: `defDoc` (header in an `IdGroup`, body by `bodyAfter`), `appDocs` with `lastArgument`/`huggedBracket` and the filled front, `chain` (flattening same-level `Binary`/`Arrow` by structural recursion, `chainLinks`/`linkDocs`), `parenDoc`, `commaBracket`/`bracketContent`, `Prefix` in `Expr.el`; `Word.leaf`, `opening`, `leading`, `trailing`, `Expr.framed` for comments | `src/Fmt/Rules.sw` | `printer/rules.rs` |
| The one gap with a choice in slice 1, after a prefix operator; `operatorTok` | `src/Fmt/Spacing.sw` | `spacing.rs` |
| `within1` (on `Expr`, `Header`, `Decl`, `SourceFile`), the alphabet `Tok.within1`, the file loop `SourceFile.printed1`, `formatWithin` | `src/Fmt/Slice1.sw` | `printer/mod.rs`'s `print_file_seeing` |
| `Comments.blankBefore`: a blank line just before the token, below its own-line comments | `Syntax/Expr.sw`, `DeclParser.sw` | `Trivia::blank_lines_before` |
| `Fmt.Twin --stage text` (a file within slice 1 formatted, else status 3 `outside slice 1`) and `--stage s1` (a line a declaration, `within` with its text, or `outside`) | `src/Fmt/Twin.sw` | |
| `dev/fmt-twin s1`: each declaration `--stage s1` says is within, against the `text` line of Rust's cached `dev doc` dump | `dev/fmt-twin` | |
| Tests | `src/Fmt/Tests/Slice1.sw` (6) | |

Continued lines, the `Def` frame, the traversal and P2 were already in (stages 2a, 2b, 4a): `formatWithin` runs `Lexed.tidied`, all four passes, which are the identity on slice 1 but for P2.

How the Rust rules' index-based reads became tree-shaped: an `Around` travels down with what a rule needs of a token's surroundings (the code before ends its line with a comment; the first token's comments are hoisted; it starts a comma-bracket item; the tokens before it in the declaration). Rust's `fresh_id` and `Mark(i)` keys are that token count: a call's `IdGroup` is keyed by its first token, which no other call in the declaration starts with, and the declaration's by 0. A stale key would matter, since `fitsFrom` reads recorded modes without recording. Every rule is structurally recursive (the first version dispatched through `Expr.node expr`, which the termination checker rightly refused).

Spacing: in slice 1 every gap Rust copies from the source is fixed by the tree, since the parser read the gap to build it (an argument minus is a `Prefix` argument, `- 2 n` a `Prefix` of an application). Two pairs remain where Rust copies and the tree can't say: `)(` and a glued `f[x]`-like pair between call elements; the rules write a space. No sampled declaration has either.

### The gate [measured, Speedwell, load about 15]

`dev/fmt-twin s1 --exe` with the interpreted twin (below):

| Input | Declarations | Within slice 1 | Matched | Mismatched |
|---|---|---|---|---|
| `goldens` (132 files) | 644 | 82 | 82 | 0 |
| `repo --sample 300` (seed 1, E3's and E4's sample) | 5,798 | 37 | 37 | 0 |

Plus a hand file of comment cases (a comment after an opener, before a closer, above an argument, a blank line before a list item, trailing comments in a broken list, a displaced bracket after `:= -- c`) and long chains, tuples and hugs: `--stage text` identical to `stitchwort fmt -`. Slice 1 is narrow: 0.6% of the repo sample's declarations.

**The native build doesn't fit in 2 GB.** A copy of `tools/fmt` without the proof files and tests (`Syntax`, `Blank`, `Meaning`, `Passes`, the slice 1 files, `DocDump`, `Twin`) peaked at 2.06 GB and was stopped. The harness ran `stitchwort run --project SLIM Fmt.Twin.main` from a wrapper script as `--exe` (850 MB, 2 s for one file, 31 s for the 300-file batch).

### For the proof lanes (13 to 20)

- **F1 lacked blank lines.** The layout-free tree had no blank line before a token, which the printer keeps between declarations, after own-line comments and before a broken list's items. `Comments.blankBefore` (a `Bool`, as `Note.blankBefore`) adds it; `Comments.none` clears it, so `meaning` doesn't see it. Sketch §1's "no count of blank lines" holds; a flag was needed.
- `within1` is on the tidied tree too; P1, P3 and P4 change nothing within slice 1 (no theorem, no row, no binder), which the passes' lemma lane can state as such.
- `Expr.words` (tokens in order) carries `trails`, `holdsTrailingComment`, `size`, `firstWord`: the rules' read-back of Rust's index lookups. They are list functions, so lemmas about them are list lemmas (F6).
- Checks of `formatWithin` stop at the first token outside the alphabet, then at a tree outside `within1` (an alphabet-only file can still parse to `(a: T)` or a parameter group); the parser-stays-in-the-slice lemma (§1.1, item 4) is what would let the second check go.

## Slice 2, the program (SW-3959)

Opus, 18 November 2026. Slice 2 (binders) on top of slice 1, as SW-3950 built slice 1.

### What is here

| Piece | Where | Rust counterpart |
|---|---|---|
| `defDoc` widened: the head (`def`/`theorem`, the name, a theorem's `∀`), parameter groups by `paramsHeader` (runs of variables as balanced fills, each premise alone, a variable between premises on the premise's line, the `:` against the last group, or starting a line after own-line comments), `groupHoldsComment` for the header's forced break | `src/Fmt/Rules.sw` | `decl`, `header`, `balanced_fill` |
| `premisesOf`, `propositionIn`, `capitalised` | `src/Fmt/Rules.sw` | `premises`, `is_proposition` |
| `groupDoc` (a `Param` or `LambdaParam` group), `Param.el`, `lambdaBoth`, `quantifier`, `effectDoc` with `rowItems` | `src/Fmt/Rules.sw` | `join` of those nodes, `lambda_both`, `lambda_head`, `quantifier` |
| A lambda in brackets as a call's last argument hugs (`huggedLambda`); a lambda after `:=` may stay on the line, its body below (D3568) | `lastArgument`, `bodyAfter` | `last_argument`, `body_after` |
| `within2`, `Tok.within2`, `Decl.printed2`, `SourceFile.printed2`; `formatWithin` now covers both slices and refuses with `outside slice 2` | `src/Fmt/Slice2.sw` | |
| `Fmt.Twin --stage s2`; `s1` and `s2` share `sliceAnswer` | `src/Fmt/Twin.sw` | |
| `dev/fmt-twin s2` (`slice_stage` takes the stage) | `dev/fmt-twin` | |
| Tests | `src/Fmt/Tests/Slice2.sw` (6) | |

The slice is the plan's row with two choices made: `Type` and `Prop` are words of the slice (most parameter groups need them, and they print as any word); and an ability row is within only before a header's result type, since Rust's spacing gives a row's braces no spaces only after `:` or `→` (`Role::Row`), and elsewhere `{ IO }`. Groups have names, `:` and a type, and no attributes, `auto` or default. `PatternWord` is in the slice as a binder parameter (`PatternParam (PatternWord …)`), but the parser never builds one there (a name or `_` is a `NameParam`), so it is vacuous.

Keys as in slice 1: every `IdGroup` and `Mark` is keyed by a token count from the declaration's start; the header's tokens count from the keyword, then the `∀`, the groups (`groupsWords`), the `:`, the type. Every rule is structurally recursive: `huggedLambda` takes the lambda's parts, not a rebuilt `Binding`, so that it recurses only into subterms.

### The gate [measured, Speedwell]

`dev/fmt-twin s2 --exe` with the interpreted twin (a slim copy as SW-3950's, `--jobs 1`):

| Input | Declarations | Within slices 1 and 2 | Matched | Mismatched |
|---|---|---|---|---|
| `goldens` (132 files) | 644 | 230 | 230 | 0 |
| `repo --sample 300` (seed 1) | 6,072 | 444 | 444 | 0 |

Slices 1 and 2 cover 7.3% of the sample's declarations (slice 1 alone: 45, 0.7%). The sample is drawn from the tracked files, so it moves with the tree: SW-3950's had 5,798 declarations, and this lane's first run, before its own files were committed, 6,061 (453 within, all matched). `dev/fmt-twin s1` stays 82 of 82 and 45 of 45. A hand file of headers (long, with premises, with comments after a group and before the `:`), lambdas (hugged, after `:=`, with a comment after `=>`, with filled parameters), long `∀` and `∃` and rows: `--stage text` identical to `stitchwort fmt -`.

**Gaps Rust copies and the tree can't tell.** Rust keeps the source's gap in `)(` (spacing.rs's `kept`), so `∀ (a: A)(b: B) => P` and `(a: A)(b: B) => a` print as written, glued; and it copies the gap after a row's `}` when there was none (`{IO}Nat`). The rules write a space in both. A header's groups are separated by the fill's line breaks, so `def f (a: A)(b: B)` gets its space in both. No sampled declaration has either.

### For the proof lanes

- The F1 tree is unchanged.
- P1, P3 and P4 are live in slice 2: `theorem t (n: Nat)` gets its `∀` and `(n: Nat) (m: Nat)` merges in a theorem's header (the first test shows both); `within2` is on the tidied tree, as `within1`.
- `printDecls2` repeats `printDecls` with `printed2`; a slice-indexed file loop would let later slices share it.

## Slice 1 lexer proofs (SW-3965, Sonnet, 18 November 2026)

`Syntax/LexProofs.sw` (namespace `Syntax.Proofs`), 150 theorems, `stitchwort audit Syntax.Proofs` clean. What is
proved, for the alphabet of slice 1 only:

- **`item` per lexeme** (`ItemReads read lexeme rest`): the 24 fixed spellings, the 7 Unicode ones, spaces, a line
  break, a comment, a name or keyword, digits and a float. Each needs a fact about the first character after it
  (`MayFollow`), stricter than the lexer where that is simpler (a `!` is never followed by `i`).
  `lexWord1` states all kinds at once from `Spells kind text`.
- **The spine**: `many` of `item` inside `recursiveWith` (`lexemesOfSteps`), so `lexCovers` for a source read
  lexeme by lexeme. `ItemReads` is about one state because a lexeme holds its offset; `runsItemsFrom` is
  `Parse.runsManyFrom` for that.
- **The layout** (`Laid`, `lexPrinted`, `lexPieces`, `lexPrintedPairs`): pieces `Code`, `Gap`, `Break`, `Remark` lex
  to the leaves with columns in bytes, line starts, own-line comments, trailing comments and blank lines. The
  concrete list `examplePieces` shows the hypotheses can be met, and `exampleLayout` is the same layout by computing.
- **One `lexesAs…` per token kind**, `operatorTokLexes`.

What is not proved: `lexCovers` for every source (it needs a theory of what a `Parse` program reads, not only that it
succeeds); `operatorTok text = Some kind` implying `Spells kind text` (the converse of `operatorTokOfSpells`); text
literals, `${…}`, characters, qualified names and `.` (outside slice 1).

The lexer was split into named parts for the proofs, with the same behaviour (`Syntax.Tests` and `Fmt.Tests` pass):
`itemAt` and `itemOn` (the input as a parameter), `wordFrom`, `qualifiedOn`, `numberFrom`, `numberTail`,
`fractionPart`, `exponentPart`, and the pure `fractionAhead` and `exponentSkip`.
