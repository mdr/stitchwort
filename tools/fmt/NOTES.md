# The self-hosted formatter: notes

The plan is `docs/proposals/self-hosted-fmt.md`. Each stage ends with a section here: its harness count, its speed numbers and friction.

## Naming and the slice gate (consolidation, SW-4214)

From 19 November 2026 the properties and functions of the tree that the proofs state facts with have one name for every slice: `shaped`, `lexical`, `settled`, `unreturned`, `operators`, `autoPlaced`, `homed`, `quiet`, `stands`, `kinds`, `spacing`, `slots`, `shapes`, `leaves`, `mapIn` and their companions (`Fmt/Predicates.sw`, `Fmt/Kinds.sw`, and the files that define the rest). A later slice adds arms to them. Their last arm is `False`: a form is shaped only once some slice's proofs cover it. Renamed where the plain name was taken or read badly: `Expr.atomic1` is `Expr.primary`, `Expr.head1` is `Expr.callHead`, `Expr.argument1` is `Expr.callArgument`, `Shape1` is `PlainShape`. Theorem names keep their numbers where they are one slice's (`printedHangs1`).

Numbered and frozen: the slice's Scope definitions (`Grammar1.sw`, `Driver1.sw`, `Slice1.sw`, `inGrammar1`, `formatWithin1`, `within1`, `alphabet1`), `Fmt/Tests/MustAccept1.sw`, and the token tables (`Tok.symbolic1`, `fixedKind1`, `Token.fixed1`, `spelledPlain1`, `movable1`, `home1`, `walk1`, `Lexed.laid1`, `Lexed.wordsSettled1`), which grow by token kind. `arrowKind1` keeps its `1`: `arrowKind` is taken.

The rules that let slice 1's lemmas stand when a property gains an arm (also in the header of `Fmt/Predicates.sw`):

1. A slice is its Scope definitions and nothing else. A property never names a slice (one exception for now: `shaped`'s atom arm reads `kind.wordWithin1`).
2. A lemma that splits on the tree's forms and needs "there is no other form" takes the gate (`within1`) and closes the other arms with the gate, not with a property's last arm. Then filling a property's arm cannot break it.
3. A lemma about one form takes facts about that node and its children and no gate (`appParsed` in `Syntax/ParseWalk.sw`). Such a lemma stands in every slice; write new forms' proof content this way.
4. A lemma with no gate that splits on a property (`argLevel`, `atomicArgument`) gains an arm when that property gains one, with its statement and callers unchanged: one property's arm and its handful of ungated lemmas in one lane.

The rationale and the counts are in `docs/proposals/fmt-consolidation-statements.md`, section 1.

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
- `tree`: `dev tree --print`'s tree without its `PATH:` header and totals line. A declaration that doesn't parse is an `Error` node in the dump, and `dev tree` exits 1; the twin answers status 1 and nothing else, so the exit status is the comparison and refusal isn't separate here.
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
| The parked comma: `Lexed.settledBare` (the last commas out, then rule N), `Lexed.settledOnce` (the last commas bare, then rule N) and `Lexed.tidied` | `Settle.sw`, `Passes.sw` |
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

Rule N parks a comma's comments on the next token; the Rust P2 then deletes the comma from the text and rule N runs again, which gives a different answer when the comma starts its line and has a comment above (proof plan §10, K1). `Lexed.settledBare` is the sketch's `withoutLastCommas` on the real leaves: Rust's comments after P2. `Lexed.tidied` parses once, from `Lexed.settledOnce`: each last comma's comments moved as `withoutLastCommas` moves them, the comma left in bare (still starting its line if it did), then rule N, which treats such a comma as if it weren't there; P2 then drops the commas on the tree (SW-3964, below). The tree dump leaves comments out, so the `passes` harness can't see this family; `the parked comma` test compares `settledBare`'s token dump with rule N's on the text with the comma written as a space, for the K1 case, and two `Tests/Slice1.sw` cases pin the formatted text.

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
- **`CommentsKept`** (in `Meaning.sw`; proved for slice 1 by `slice1KeepsComments`, `Fmt/CommentsKeptProof.sw`, SW-4203): between the source's leaves after `settledBare` (rule N with P2's commas out, so K1's moves are in it) and the output's after rule N, (1) `commentViews` equal: every comment's text, own-line or trailing, blank line above, in order, the file's end included; (2) `holders` equal: the comment-holding tokens in order with their text, count above, trailing or not, and (3) whether a blank line separates the comments above a token from it. Two blank lines are left out (D3695, Matt, 19 Nov 2026), as no doc reads them and the printer drops them: the one above the file's first comment (`unheaded`; `calmTop` tops it), and a closer's below its comments (`Holder.forDocs`; `calm` clears it). The proof reads both sides as the comments of the tree's words: the source's through `parseCarriesSourceProved` and `bareSettles`, the output's through `printedSettle1`, and `calmTop` keeps every comment and holder but those two flags (`calmTopKeeps`). `Fmt/Tests/CommentsKept.sw` (SW-4233) pins 22 sources.
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

No axioms (`stitchwort axioms Fmt.MeaningProofs.firstThreeKeepMeaning`).

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

Spacing: in slice 1 every gap Rust copies from the source is fixed by the tree, since the parser read the gap to build it (an argument minus is a `Prefix` argument, `- 2 n` a `Prefix` of an application). One pair remains where Rust copies and the tree can't say: `)(`; the rules write a space. A glued `f[x]`-like pair between call elements is spaced by both now (SW-4459). No sampled declaration has either.

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

**Gaps Rust copies and the tree can't tell.** Rust keeps the source's gap in `)(` (spacing.rs's `kept`), so `∀ (a: A)(b: B) => P` and `(a: A)(b: B) => a` print as written, glued. The rules write a space. A row's `}` when the source glued it (`{IO}Nat`) is spaced by both now (SW-4459). A header's groups are separated by the fill's line breaks, so `def f (a: A)(b: B)` gets its space in both. No sampled declaration has either.

### For the proof lanes

- The F1 tree is unchanged.
- P1, P3 and P4 are live in slice 2: `theorem t (n: Nat)` gets its `∀` and `(n: Nat) (m: Nat)` merges in a theorem's header (the first test shows both); `within2` is on the tidied tree, as `within1`.
- `printDecls2` repeats `printDecls` with `printed2`; a slice-indexed file loop would let later slices share it.

## Slice 3, the program (SW-3961)

Opus, 18 November 2026. Slice 3 (the layout core) on top of slices 1 and 2.

### What is here

| Piece | Where | Rust counterpart |
|---|---|---|
| `blockDoc` (each line at the block's column, a blank line above a later line kept), `Statement.el` | `src/Fmt/Rules.sw` | `block` |
| `letDoc`: the line up to `:=` in an `IdGroup` keyed by the `let`'s token count + 1, the value by `bodyAfter`; an expression `let`'s value on the `:=` line unless a comment or block puts it below | `src/Fmt/Rules.sw` | `let_line` with `expr_let` |
| `letInDoc`: `let x := e; body` in an `Align`, a `Line` after the `;` | `src/Fmt/Rules.sw` | `sequence` for `LetExpr` |
| `ifDoc`, `ifClauses`: one clause a line, each a group, `else if` flattened unless a comment puts the `if` below its `else`, a `BreakParent` for three or more clauses | `src/Fmt/Rules.sw` | `if_` |
| `matchParts` (the doc and the `:=` hug), `armLines`, `Arm.el`, `armDoc`, `guardDocs`, `Pattern.el` (a constructor pattern as a call of plain arguments, `_` joined to the item before it) | `src/Fmt/Rules.sw` | `alternatives`, `arm`, `app` for `PatternCtor`, `fill_items` |
| `Around.inArm` (`arm_depth > 0`): set for an arm's contents and for a `match` an operator chain starts with | `src/Fmt/Rules.sw` | `arm_depth` |
| Where a block may stand: `Expr.after` (`join`'s block rule), `parenDoc`, `huggedBlock`, `chainLinks`'s right operand, `bodyAfter` (always below); `parenDoc` aligns a bracketed `if`; `lambdaBoth`'s `semi`; `defDoc`'s `layoutBody` comment rule | `src/Fmt/Rules.sw` | `join`, `paren`, `last_argument`, `chain`, `body_after`, `lambda_both`, `decl` |
| `within3`, `Tok.within3`, `Decl.printed3`, `SourceFile.printed3`; `formatWithin` now covers slices 1 to 3 and refuses with `outside slice 3` | `src/Fmt/Slice3.sw` | |
| One file loop for every slice: `SourceFile.printedBy printed` and `printDecls printed`; `printDecls2` is gone | `src/Fmt/Slice1.sw` | `print_file_seeing` |
| `Fmt.Twin --stage s3`, `dev/fmt-twin s3` | `src/Fmt/Twin.sw`, `dev/fmt-twin` | |
| Tests | `src/Fmt/Tests/Slice3.sw` (7) | |

The slice: blocks of `let` lines and expression lines (no local `def`); `let p := e` and `let p: T := e`; `let x := e; body`; `if` without a binder (`if h: c`); `match` without named scrutinees (`h: e`), every arm with a body; patterns that are a name, `_`, a numeral, or a constructor applied to those; guards without a binder. Tuple, list and record patterns are slice 4's pattern family.

Two exclusions where Rust's output isn't the tree's to give:

- **A later block line starting with `-`.** Rust copies the source's gap after it (`StatementMinus`: `-y` right after a line ending in an operand reads as an argument), so `- z` and `-z` print as written. Two golden declarations (`negative-arguments`, declaration 9, before and after) have it; `within3` leaves such a block out.
- **A block as a quantifier's body.** Rust prints `∀ x => let y := x⏎  y = y` with the block after `=>` and its later lines left of its first, which doesn't read back (`stitchwort fmt` refuses the file as a formatter bug). `within3` asks a quantifier's body to be inline.

And one the rules handle only at the top: an expression `let`'s value that is a lambda keeps its body after `=>` (a body starting a line would be a block, which the `;` would end); Rust does that for any lambda ending just before the `;`, which the tree can't see from inside the value. `keepsLine` leaves out a value with a lambda at its end below the top.

Keys: the declaration's `IdGroup` is 0; a call's front and a `let` line's are their first token's count + 1 (no call starts with `let`); `Mark`s are an opener's count.

### The gate [measured, Speedwell]

`dev/fmt-twin s3 --exe` with the interpreted twin (a slim copy as before, `--jobs 1`):

| Input | Declarations | Within slices 1 to 3 | Matched | Mismatched |
|---|---|---|---|---|
| `goldens` (132 files) | 644 | 288 | 288 | 0 |
| `repo --sample 300` (seed 1) | 6,072 | 576 | 576 | 0 |

Slices 1 to 3 cover 9.5% of the sample's declarations (1 and 2: 444, 7.3%). `dev/fmt-twin s1` stays 82 of 82 and 45 of 45, `s2` 230 of 230 and 444 of 444. Hand files of blocks with blank lines and comments, `let` with a comment after `:=`, `if` with comments after the condition, before a branch and after `else`, `else` and a comment then `if`, a `match` with guards, a blank line between arms, a comment after the last parameter before a `match` body, a `match` after an operator, as an argument in brackets and as a `let` value, nested `match`es, a block in brackets and as a lambda's body, an `if` holding a `match`: `--stage text` identical to `stitchwort fmt -`.

What keeps the rest of the sample out [measured with `dev tree --print`, my own 300-file sample, by node kind; text literals not counted]: of 5,294 declarations, the one kind outside slices 1 to 3 is `FieldAccess` for 478, `Test` 392, `Namespace` 137, `Import` 124, a definition's `Arms` 105, `PatternList` 63, `NamedArg` 51, `Unit` 32. Field access alone would roughly double the coverage.

### For the proof lanes

- **The F1 tree is unchanged.**
- **Columns the read-back proofs need (K3b).** Every rule that puts a block somewhere starts it on a line of its own at +2 from the indentation in force (`Expr.after`, `parenDoc`, `huggedBlock`, `chainLinks`, `bodyAfter`'s below), or after a `Line` at +2 in a group the block forces broken (an `if` branch, a lambda's body), so a block's first line and its later lines (`HardLine`, no `Nest` of its own) start at the same column, which is right of the enclosing limit. Arms are at +2 from the indentation in force, not from the `match` keyword (a `match` hugging `:=` has its keyword at column 14 and its arms at 2); they read back because `|` can't begin an expression, as a continued line. A `match` inside an arm, or opening an operator chain, puts even a single arm on its own line (`inArm`): on the `with` line, the next outer arm would read as its own. `else` and `then` lines are at the `if`'s indentation in force, which inside brackets is the `if`'s column (`Align`); after `:=` or `=>` and as a block's line a broken `if` starts its line (`bodyAfter` gives it only flat or below), so the two agree; after an operator it doesn't, and its `else` lines, left of the `if`, read back as continued lines (`else` can't begin an expression). An expression `let`'s body is at the `let`'s column (`Align`), after a line ending in `;`.
- **Rule N's bar.** The arms' `|` hold own-line comments as any token does (printed above the arm at the arms' column, a blank line above kept, `item`); no new comment placement.
- P1 to P4 change nothing new in slice 3: no theorem headers or rows inside blocks beyond slice 2's.
- `bodyAfter` builds a `match` value once and takes its hug from the same parts; a call's hug is still built twice, as before.

## Slice 1 lexer proofs (SW-3965, Sonnet, 18 November 2026)

`Syntax/LexProofs.sw` (namespace `Syntax.LexProofs`), 150 theorems, `stitchwort audit Syntax.LexProofs` clean. What is
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

## Family A fixed, and the search kept (SW-3962, Opus, 18 November 2026)

**The cause.** A closer that rule N leaves after code ending its line with a comment, and that has a comment of its own, takes a line of its own (S39, `leaf` and `Word.leaf`). That line was a `HardLine`, at the indentation in force. In a declaration's type the bracket's contents, pushed below `(` by the comment, are at that same indentation (4), so the closer started a line at its contents' column and the parser read it as their block's next line: sketch §3.1, family A. Elsewhere the contents sit 2 right of the indentation in force (a call's argument, a body), which is why only the type showed it.

**The fix, both formatters.** That line is a `CloserLine` keyed by the bracket's opener, as for a closer after own-line comments (S40, SW-3605): it goes back to the opener's line's indentation when a line inside is at or left of the indentation in force, and stays put otherwise. The opener gets its `Mark` whenever the closer may take a line of its own: own-line comments before it, a comment after it, or (Rust only, outside the slices) a glued `.field`. `def d: ( -- t7⏎    a -- t9⏎  ) -- t10⏎  := b` now prints `)` at 0 and `:=` at 2 in both. No golden file moved; the slice gates are unchanged (s1, s2, s3 100% on the goldens and the 300-file sample).

**The search** is in `dev/` (`README.md` says how to build the interpreted twin and run it). Rerun on slice 1, seeds 8 and 9, 1,500 files each [run]: 1,758 formatted, 0 idempotence, tree, comment or long-line failures, `hangs.py` clean (family A was 9 of 5,611 before). SW-3955's nine family A files format to text that parses in both formatters, and identically but for one, whose difference is family D's. The generator is slice 1's only; slices 2 and 3 would need a generator of binders, blocks and `if`s.

## Slice 4a, the program (SW-3980)

Opus, 18 November 2026. Field access, the first part of the plan's S4 row, on top of slices 1 to 3: SW-3961 found it the only construct outside S1–S3 for 478 of 5,294 sampled declarations.

### What is here

| Piece | Where | Rust counterpart |
|---|---|---|
| `FieldAccess (Some target) dot field` in `Expr.words` and `Expr.el` (the target, `.`, the field, nothing between them) | `src/Fmt/Rules.sw` | `join` (Rust has no rule of its own for `FieldAccess`); `spacing.rs` keeps the source's gap at a `.`, which the parser requires to be none |
| `Expr.simple` for a field of a simple expression (`a.b.c` stays on a broken call's line) | `src/Fmt/Rules.sw` | `simple`'s `FieldAccess` arm |
| `within4a` (on `Expr`, `Header`, `Decl`, `SourceFile`), the alphabet `Tok.within4a` (slice 3's and `.`), `Decl.printed4a`, `SourceFile.printed4a`; `formatWithin` moves here from `Slice3.sw`, covers slices 1 to 4a and refuses with `outside slice 4a` | `src/Fmt/Slice4a.sw` | |
| `Fmt.Twin --stage s4a`, `dev/fmt-twin s4a` | `src/Fmt/Twin.sw`, `dev/fmt-twin` | |
| Tests | `src/Fmt/Tests/Slice4a.sw` (3); slice 1's refusal test now uses a method section, since `r.field` is within | |

**The slice's edge.** Rust prints a field access with the generic `join`, so it never breaks, however long the `.a.b.c` chain: there is no chain rule for fields. A dot call `xs.map f` is an `App` whose function is a `FieldAccess`, printed by `app` as any call, so it comes free. Headers are widened too (a theorem's statement often reads `xs.length = …`): `Header.within4a` is `within2` with field access in the parameter types and the result type. Left out:

- **A method section `.f`** (`FieldAccess None` inside a `Section`): S4's sections; it brings `section`'s rule that `.f` can't start a line.
- **`f()`**: `Unit`, S4's.
- **A field after a bracket whose contents end their line with a comment**, `(x -- c⏎).f`: Rust keeps that closer on a line of its own, keyed to a `Mark` on the opener (`glued_field`, SW-3962). The tree can say it (the target `trails`), but the closer's leaf doesn't know a `.` follows; `within4a` asks the target not to trail. No golden or sampled declaration has it.
- **`- 1.abs`**: after a `-` before a numeral followed by `.`, Rust copies the source's gap (`- 1.abs` is not `-1.abs`, D1474), and the tree is the same either way. `within4a` leaves out a `-` whose operand starts with a numeral and a `.`. `-1.abs` written glued parses as a field of `Prefix - 1` and is within.

Keys as before: the `.` and the field each count one token, so a field access's tokens are its target's, then two.

### The gate [measured, Speedwell]

`dev/fmt-twin s4a --exe` with the interpreted twin (a slim copy as before, with `Slice4a.sw` and without `Syntax/LexProofs.sw`; a fresh `FMT_TWIN_CACHE`, `--jobs 1`):

| Input | Declarations | Within slices 1 to 4a | Matched | Mismatched |
|---|---|---|---|---|
| `goldens` (132 files) | 644 | 304 | 304 | 0 |
| `repo --sample 300` (seed 1) | 5,854 | 963 | 963 | 0 |

Slices 1 to 4a cover 16.4% of the sample's declarations; slices 1 to 3 cover 554 of the same 5,854 (9.5%), so field access adds 409 (the sample moved with the tracked files again: SW-3961's had 6,072). The goldens gain only 16, since they exercise layout rather than fields. On the same runs `s1` stays 82 of 82 and 39 of 39, `s2` 230 of 230 and 426 of 426, `s3` 288 of 288 and 554 of 554. Hand files of chains, dot calls with hugged lambdas, fields in a theorem's statement, `a.b` kept on a broken call's line, a field after a trailing comment, and `-1.abs` against `- 1.abs`: identical to `stitchwort fmt -` (the last two kinds refused as outside).

### For the proof lanes

- **The F1 tree is unchanged.**
- **No new columns.** A field access never breaks and puts nothing on a line of its own, so the read-back proofs need no new column fact: `.` and the field are glued to the target's last token on its line. What they need is lexical: a `.` glued on both sides reads back as a field access (the parser refuses a spaced one), and the target's last token is never a comment's (`within4a`'s `!target.trails`), so nothing comes between.
- **Spacing.** The one gap a field access adds is `- 1.f`'s, left out above; `prefixGap` is unchanged.
- P1 to P4 change nothing new: a field access holds no binder, row or theorem header.

## Slice 5a, the program (SW-3990)

Opus, 18 November 2026. The declarations around definitions, and a definition's own arms, on top of slices 1 to 4a: SW-3961's count put `test` (392), `namespace` (137), `import` (124) and a definition's arms (105) next after field access.

### What is here

| Piece | Where | Rust counterpart |
|---|---|---|
| `namespaceDoc`: the keyword, a space, the name | `src/Fmt/Rules.sw` | `join` (no rule of its own) |
| `importDoc`, `importItemDocs`, `ImportItem.el`: `import M (` then the items as a comma bracket, flat if it fits, else one a line at 2 and `)` alone; an item framed as a node (a comment before it displaces it); `(..)` as one item | `src/Fmt/Rules.sw` | `import`, `comma_bracket` |
| `testDoc`: `test "name"` in an `IdGroup` (a comment after `test` breaks it), then `:=` and the body by `bodyAfter` | `src/Fmt/Rules.sw` | `decl` with a head and a body |
| `defArmsDoc`: the header as `defDoc`'s, built inside the arms' depth (`inArm`), then `armLines` at 2, one arm a line | `src/Fmt/Rules.sw` | `decl` with `Arms` |
| `within5a`, `Tok.within5a` (slice 4a's, `namespace`, `import`, `test`, `..`, text and character literals), `Decl.doc5a`, `Decl.printed5a`, `SourceFile.printed5a`; `formatWithin` moves here from `Slice4a.sw` and refuses with `outside slice 5a` | `src/Fmt/Slice5a.sw` | |
| `Decl.firstComments` covers `namespace`, `import` and `test` | `src/Fmt/Slice1.sw` | `print_file_seeing` |
| `Fmt.Twin --stage s5a`, `dev/fmt-twin s5a` | `src/Fmt/Twin.sw`, `dev/fmt-twin` | |
| Tests | `src/Fmt/Tests/Slice5a.sw` (5) | |

**The file loop.** A `namespace` here is a line, not a block: the declarations after it are the file's, at column 0, so `printedBy` needed nothing new. Blank lines between declarations are as for definitions: the first token's `blankBefore` (one blank line at most, as Rust's `blank_lines_before > 0`), with own-line comments above a declaration printed by the file, each keeping a blank line above it.

**The slice's edge.** Tests name themselves with text and most compare texts, so one-line text and character literals are in the slice (a token each, `simple` and a plain list item as Rust has them). Left out: a text block (a literal spanning lines, which Rust moves with its line, `TextBlock`) and interpolated text; `instance`, attributes, `export`, `opaque`, `decreasing` and `unfolding` (as before); arms whose patterns are tuples, lists, records or `(p)` (S4's patterns). A literal glued to the token before it (`f"x"`) is spaced by both now (SW-4459); no sampled declaration has one.

### The gate [measured, Speedwell]

`dev/fmt-twin s5a --exe` with the interpreted twin (a slim copy as before, with `Slice5a.sw` and without `Syntax/LexProofs.sw`; a fresh `FMT_TWIN_CACHE`, `--jobs 1`):

| Input | Declarations | Within slices 1 to 5a | Matched | Mismatched |
|---|---|---|---|---|
| `goldens` (132 files) | 644 | 336 | 336 | 0 |
| `repo --sample 300` (seed 1) | 5,527 | 2,274 | 2,274 | 0 |

Slices 1 to 5a cover 41.1% of the sample's declarations; slices 1 to 4a cover 909 of the same 5,527 (16.4%). On the same runs `s1` stays 82 of 82 and 41 of 41, `s2` 230 of 230 and 420 of 420, `s3` 288 of 288 and 539 of 539, `s4a` 304 of 304 and 909 of 909. A hand file of a commented namespace line, flat, broken, `(..)` and commented imports with a blank item, tests with literals, a long body and a comment after `test`, a test with a `match`, and arms with comments, a blank line, a header with merged parameters and a theorem with a comment after its type: `--stage text` identical to `stitchwort fmt -`.

What keeps the rest out [measured: the twin's `s5a` answers against `dev tree --print`'s node kinds on the same sample; a kind is foreign if no within declaration has it]: of 3,253 declarations outside, 385 have no foreign kind (a shape the slice refuses), 2,039 two or more. With one foreign kind: `PatternList` 205, `PatternAbsurd` 112, `Annotation` 77, `NamedArg` 50, `Membership` 46, `Unit` 42, `PatternTuple` 39, `Spread` 27. Any foreign kind: `Rewrite` 734, `PatternList` 719, `Record` 534, `Spread` 300, `PatternAbsurd` 294, `Unit` 236, `Membership` 235, `Binder` 223. Proofs (`rewrite`) and list patterns lead.

### For the proof lanes

- **The F1 tree is unchanged.**
- **No new columns beyond slice 3's.** A definition's arms are at 2, as a `match`'s arms are from the indentation in force (0); `|` can't begin an expression, so they read back. A broken import's items are at 2 with `)` at 0, a comma bracket's shape. A namespace line and a test's head never break.
- **Rule N's bar.** Nothing new: an import item holds own-line comments as a list item does (`item`, a blank line above kept).
- `defArmsDoc` repeats `defDoc`'s header lines rather than changing `defDoc` while slice 1's proofs are being written against it; a shared header function would let them go.

## Slice 4b, the program (SW-3992)

Opus, 18 November 2026. The patterns of the plan's S4 row, on top of slices 1 to 5a: SW-3990's census put `PatternList` (205), `PatternAbsurd` (112), `Annotation` (77), `NamedArg` (50) and `PatternTuple` (39) among the constructs alone in keeping a declaration out.

### What is here

| Piece | Where | Rust counterpart |
|---|---|---|
| `Pattern.el` for `(p)` and `()` (the brackets and what they hold), tuple and list patterns (`patternBracket`, `patternCells`, `brokenPatterns`: flat if it fits, else one item a line at 2 and the closer alone; a tuple of only names and `_` fills its lines; a list's `..rest` the last item, glued), and a constructor with an argument that is no token (`patternApp`: flat, else its leading tokens on the line and each other argument below) | `src/Fmt/Rules.sw` | `join`, `comma_bracket_content` (its `pattern_names` case), `app` with no hug |
| `Pattern.words` for the new patterns, `tailWords`, `Pattern.simple` | `src/Fmt/Rules.sw` | `simple`: no pattern but a token is simple, `[]` included |
| An absurd arm, with no `=>`: its tokens on a line, in `armDoc` | `src/Fmt/Rules.sw` | `arm`'s `join` when there is no `=>` |
| `namedArgDoc` (`(n := e)`) and `annotationDoc` (`(e: T)`), in `Expr.el` and `Expr.words` | `src/Fmt/Rules.sw` | `join` (no rule of their own) |
| `within4b` (on `Expr`, `Pattern`, `Arm`, `Let`, `Header`, `Decl`, `SourceFile`), `Tok.within4b` (slice 5a's alphabet, which has every token these need), `Decl.printed4b`, `SourceFile.printed4b`; `formatWithin` moves here from `Slice5a.sw` and refuses with `outside slice 4b` | `src/Fmt/Slice4b.sw` | |
| `Fmt.Twin --stage s4b`, `dev/fmt-twin s4b` | `src/Fmt/Twin.sw`, `dev/fmt-twin` | |
| Tests | `src/Fmt/Tests/Slice4b.sw` (6); slice 1's and 5a's refusal tests now use the unit and a record pattern, since annotations and list patterns are within | |

**The slice's edge.** Patterns are in arms (a `match`'s and a definition's) and after `let`; a lambda's parameters are still names, `_` and groups. Left out:

- **Record patterns** and a constructor's named fields (records), `p | q` inside brackets, `-1`, `"a" ++ rest`, `(n := p)`.
- **Gaps Rust copies that the tree can't say:** `.._` (after `..` Rust keeps the source's gap unless a name or bracket follows), `()` as a constructor's argument, and the unit `()` anywhere (`f ()` against `f()`, D1039). The unit is now the construct most often alone in keeping a declaration out (133); taking it needs the gap in the tree, or `within` to allow it only where no name comes before it.
- **Comments on a list's `..`**.

A tuple pattern of names fills its lines as a list of plain values does; SW-3963's family B fix (a blank line before a filled list's first cell) will want the same change in `patternCells` once both are in.

### The gate [measured, Speedwell]

`dev/fmt-twin s4b --exe` with the interpreted twin (a slim copy with `Slice4a.sw`, `Slice5a.sw` and `Slice4b.sw`, without `Syntax/LexProofs.sw`; a copied binary with `STITCHWORT_STD_DIR`; a fresh `FMT_TWIN_CACHE`, `--jobs 1`):

| Input | Declarations | Within slices 1 to 5a and 4b | Matched | Mismatched |
|---|---|---|---|---|
| `goldens` (132 files) | 644 | 352 | 352 | 0 |
| `repo --sample 300` (seed 1) | 5,888 | 2,741 | 2,741 | 0 |

The slices cover 46.6% of the sample's declarations; slices 1 to 5a cover 2,368 of the same 5,888 (40.2%; SW-3990 measured 41.1% of a sample of 5,527, which has moved with the tracked files), so slice 4b adds 373. On the same runs `s1` stays 82 of 82 and 41 of 41, `s2` 230 of 230 and 434 of 434, `s3` 288 of 288 and 564 of 564, `s4a` 304 of 304 and 969 of 969, `s5a` 336 of 336 and 2,368 of 2,368. Hand files of list patterns with tails, nested tuples and `(p)`, an absurd arm, tuple patterns after both kinds of `let`, a long list pattern, a long tuple of names, a comment after `[`, a constructor with a list argument past the width, named arguments (flat, broken, commented) and annotations (flat and broken): `--stage text` identical to `stitchwort fmt -`.

What keeps the rest out [measured, as SW-3990's count]: of 3,147 declarations outside, 642 have no foreign kind (a shape the slice refuses, up from 385: the declarations the new kinds let in as far as their next refusal), 1,879 two or more. With one foreign kind: `Unit` 133, `Spread` 114, `Membership` 81, `PatternRecord` 35, `Pipe` 32, `Section` 27, `Omega` 27, `Chain` 21. Any foreign kind: `RewriteRule` 769, `Rewrite` 768, `Record` 581, `RecordField` 526, `Spread` 347, `Unit` 274, `Membership` 235, `Binder` 232.

### For the proof lanes

- **The F1 tree is unchanged.**
- **Columns.** A broken tuple or list pattern puts its items at 2 from the line it opens on and its closer at that line's indentation, a comma bracket's shape; in an arm's head that is inside the head's `Nest 2`, so items at 4 and the closer at 2 from the arm's `|`, as Rust has them. A filled tuple pattern continues at 2. A constructor whose arguments break puts each non-token argument on a line at 2 (4 when its leading tokens fill). An absurd arm is one line.
- **Rule N.** A named argument or annotation is a bracket pair like `(e)`: its opener's `Mark` and its closer's own line come from `opening` and `leaf` as `parenDoc`'s do.
- P1 to P4 change nothing new: no binder, row or theorem header is added.

## Families B and D fixed (SW-3963, Sonnet, 18 November 2026)

- **B, a blank line before a list's first item:** in a list of only plain values (and a tuple pattern of only names and `_`, SW-3992's filled form) the first item is no item for blank lines, in both formatters (`firstAround`; Rust skips `mark_item` for it). A filled list wrote nothing for that blank line mid-line but its `BreakParent` still broke the groups around it, so `def d: A := g [⏎⏎  f, a]` formatted to three lines and then to one. Rust keeps no blank line before a block's first line either, so dropping it matches the rest. The test is "plain" without the no-trailing-comment condition of the filled form, so `calm` (`calmItems`, `pickItems`) can decide it from the items alone: `calm`'s proofs then need only that `calm` keeps which items are plain (`exprCalmPlain`). A plain list holding a trailing comment (broken, not filled) also loses the blank before its first item.
- **D, `withoutLastCommas`:** a comma that starts its line hands its trailing comment to the closer with the comma's blank line; a comma alone on its line leaves a blank before the closer's first own-line comment, as Rust deleting the comma from the text does (the line is empty). The second case was the one sampled file (x909) left once the first was fixed.
- Gates after both: `s1` to `s5a` and `s4b` 100% on goldens and a 300-file sample. Search (seeds 8 and 9, 1,500 files each): 0 non-idempotent, 0 tree, comments or long-line failures; 118 and 102 files differ from Rust, all glued call elements (§3.5) or a closer after own-line comments with a trailing comment, none family B or D.

## Slice 4c, the program (SW-3995)

Opus, 18 November 2026. The records of the plan's S4 row, and membership, on top of slices 1 to 5a and 4b: SW-3992's census put `Record` (581), `RecordField` (526) and `Spread` (347) among the kinds most often in a declaration kept out, and `Spread` (114), `Membership` (81) and `PatternRecord` (35) among those alone in keeping one out.

### What is here

| Piece | Where | Rust counterpart |
|---|---|---|
| `recordContent`, `recordItems`: `{ a = 1, b }` flat if it fits, else each field on a line at 2 and `}` alone; an update's `{ r \|` stays on the opener's line; never filled | `src/Fmt/Rules.sw` | `comma_bracket_content` with brace edges (`Line`, not `SoftLine`), its update case |
| `recordFieldDoc` (`name = value`), `CtorFields` (`C { … }`), `Spread` (`..xs`, glued), `membershipDoc` (`x ∈ s`, never broken) in `Expr.el` and `Expr.words` | `src/Fmt/Rules.sw` | `join` (no rules of their own) |
| A record hugs as a call's last argument (`huggedRecord`) and after `:=` or `=>` (`bodyAfter`'s `opens`: on the line, or one line below when it fits there, D3571) | `src/Fmt/Rules.sw` | `huggable`, `last_argument`, `body_after` |
| `fieldsContent`, `fieldItems`, `FieldPattern.el`: record patterns `{ a, b = p, .. }` as records; `fieldsJoined` for `C { a, .. }`, on one line | `src/Fmt/Rules.sw` | `comma_bracket_content` for `PatternRecord`; `join` for `PatternCtorFields`, whose braces and fields are the constructor's children in Rust's tree |
| `within4c` (on `Expr`, `Pattern`, `FieldsPattern`, `Arm`, `Let`, `Header`, `Decl`, `SourceFile`), `Tok.within4c` (slice 4b's and `∈`, `∉`), `Decl.printed4c`, `SourceFile.printed4c`; `formatWithin` moves here from `Slice4b.sw` and refuses with `outside slice 4c` | `src/Fmt/Slice4c.sw` | |
| `Fmt.Twin --stage s4c`, `dev/fmt-twin s4c` | `src/Fmt/Twin.sw`, `dev/fmt-twin` | |
| Tests | `src/Fmt/Tests/Slice4c.sw` (6); slice 4b's and 5a's refusal tests now use a negative pattern and pipes, since record patterns and records are within | |

**The slice's edge.** Records are in values, arguments, headers' types and theorem statements (`{ p | x = 3 }.x = 3`); record patterns in arms, after `let` and as a constructor's argument. Left out:

- **Gaps Rust copies that the tree can't say:** the empty record `{}` and pattern `{}` (Rust keeps the gap between the braces), and a spread whose list starts with anything but a name or a bracket (`..` before anything else keeps the source's gap, as for a list pattern's tail).
- **A record beside a call element is spaced by both:** a record right after a name or closer, or a name or bracket right after a record's `}`, as a call's arguments (`f{ a = 1 }`, `{ a = 1 }x`), gets a space from `spacing.rs`'s adjacent-call-elements rule (SW-4459), as the slice already did. The gate's 100% says no sampled declaration has one glued. The same holds for a record pattern after a constructor's earlier argument.
- **Comments** after a spread's `..`, after an update's record (Rust moves that comment past the `|`, `defer_trailing`, SW-3487), and anywhere in a `C { … }` pattern (printed by `join`, whose bracket keys the slice doesn't need yet).
- **`C { … }` after anything but a plain constructor name**, field values that are blocks, and what slice 4b left out (the unit, sections, pipes, `rewrite`).

### The gate [measured, Speedwell]

`dev/fmt-twin s4c --exe` with the interpreted twin (a slim copy with `Slice4a.sw` to `Slice4c.sw`, without `Syntax/LexProofs.sw`; a copied binary with `STITCHWORT_STD_DIR`; a fresh `FMT_TWIN_CACHE`, `--jobs 1`):

| Input | Declarations | Within slices 1 to 5a, 4b and 4c | Matched | Mismatched |
|---|---|---|---|---|
| `goldens` (132 files) | 644 | 410 | 410 | 0 |
| `repo --sample 300` (seed 1) | 5,947 | 3,320 | 3,320 | 0 |

The slices cover 55.8% of the sample's declarations; slices 1 to 5a and 4b cover 2,858 of the same 5,947 (48.1%; SW-3992 measured 46.6% of a sample of 5,888, which has moved with the tracked files), so slice 4c adds 462. On the same runs `s1` stays 82 of 82 and 38 of 38, `s2` 230 of 230 and 438 of 438, `s3` 288 of 288 and 575 of 575, `s4a` 304 of 304 and 1,004 of 1,004, `s5a` 336 of 336 and 2,477 of 2,477, `s4b` 352 of 352 and 2,858 of 2,858. A hand file of literals, punned fields, updates flat and broken, a record hugged by a call, comments inside a record and after `=`, a constructor's fields, spreads, membership in a header and a body, record patterns flat and broken in an arm, after `let` and after a constructor, and a field of an update in a theorem's statement: `--stage text` identical to `stitchwort fmt -`.

What keeps the rest out [measured, as SW-3990's count]: of 2,627 declarations outside, 759 have no foreign kind (a shape the slice refuses), 1,440 two or more. With one foreign kind: `Unit` 117, `Instance` 42, `Omega` 40, `Section` 33, `Pipe` 30, `Iff` 25, `Chain` 24, `OperatorSection` 19. Any foreign kind: `RewriteRule` 799, `Rewrite` 798, `Unit` 239, `Binder` 230, `Section` 197, `Pipe` 190, `FunctionType` 137, `Fields` 122. Of the 759 shapes, 71 hold a record, 40 a membership and 23 a spread; why each is refused wasn't looked into. The unit is now the clear next construct, then proofs.

### For the proof lanes

- **The F1 tree is unchanged.**
- **Columns.** A broken record puts its fields at 2 from the line it opens on and `}` at that line's indentation, a comma bracket's shape with brace edges; an update's `{ r |` is that first line. A broken record pattern in an arm's head is inside the head's `Nest 2`: fields at 4 and `}` at 2 from the arm's `|`, as a list pattern's. Membership, a spread, a record field's `name =` and `C { … }` patterns never break between their tokens; a field's value may break as the value does elsewhere.
- **Rule N.** A record's `{` and `}` are a bracket pair as a list's: the opener's `Mark` and the closer's own line come from `opening` and `leaf`.
- **Spacing.** New gaps: a space inside a record's braces and around `=`, `|`, `∈` and `∉`; none after a spread's `..` (the list starts with a name or bracket). The copied gaps above are the open ones.
- P1 to P4 change nothing new: membership was already a proposition for `premises` (`propositionIn`), and no binder or row is added.

## Slice 1 rules proofs, first half (SW-3970, Sonnet, 18 November 2026)

Ticket 18a of the proof plan. Three files beside `Rules.sw`; `audit` of each: `Fmt.CalmProofs` 139 theorems, `Fmt.SpellProofs` 126, `Fmt.PrintLexProofs` 41, 0 failed, 0 warnings.

### What is proved

- **`calmPrints`** (`Fmt/CalmProofs.sw`, namespace `Fmt.CalmProofs`): `file.within1`, `file.lexical` give `file.calm.printed1 = file.printed1`. `lexical` is only used for its closers (`Expr.closed`: a bracket's last word is a closer, which `calm` clears as one; a closer word of other text would be read as a token and its flag lost). The proof is by `elCalm` (induction on the expression, each rule's lemma taking the hypothesis for its parts as `ElKept`), `defDocKept` for the declaration and `printDeclsCalm` for the file loop. Groups: words that `calm` keeps (`Word.alike`, `wordsCalm`, `firstCalm`, `sizeCalm`, `trailsCalm`, `holdsCalm`, 20), what `leading` reads (`leadingKept`, `leafKept`, `openingKept`, 6), chains (`chainKept`, `linkDocsKept`, 8), brackets and calls (`bracketKept`, `huggedKept`, `lastArgumentKept`, `argumentDocsKept`, `appKept`, 25), the body and the definition (`bodyAfterKept`, `defDocKept`, `plainDefKept`, 20), the file (`declPrintedCalm`, `calmPrints`, 17), parts of a good expression (27).
- **`printedSpells`** (`Fmt/SpellProofs.sw`, namespace `Fmt.SpellProofs`): for `decl.within1` and `decl.sound` (every token's text isn't layout, its comments are as rule N leaves them), at any width, `wordsOf (printedPieces doc width)` filtered to drop closers and commas is the tree's spelling filtered the same, and filtered to drop comments likewise. Two statements, because `Std.Doc`'s `printedWords` lets a closer and a trailing comment change places on a line (a `Closing` is written before the comment waiting there). `Decl.spelt` is each token's own-line comments, text and trailing comment in the tree's order, a comma between a bracket's items; the keyword's own-line comments are the file's. `printedSpellsSettled` takes `settled` and `Decl.real` (no token's text is layout) instead of `sound`; `printedSpellsText` ties it to `Decl.printed1`. The pieces: `Spells doc texts` (the document's words, `Uniform`, `Marked`) with one combinator per `Doc` constructor (23), one lemma per rule function (`leafSpells`, `openingSpells`, `framedSpells`, `parenSpells`, `bracketFromSpells`, `cellsSpells`, `brokenItemsSpells`, `appFromSpells`, `argumentDocsSpells`, `chainLinksSpells`, `bodyAfterSpells`, `plainDefSpells`, `elSpells`), and the bridge from `settled` (11).
- Witnesses: `exampleDecl` (`def d: A := g [a, b]`) meets the hypotheses of both (`printedSpellsExample`, `calmPrintsExample`).
- `Fmt.Tests` (`Tests/RuleProofs.sw`, 4 tests): the hypotheses and the proved equalities hold of the tidied tree of files with comments in every gap, parsed by the real parser.

### Splits in `Rules.sw` (behaviour kept: `Fmt.Tests` 82 of 82 before the new tests)

`parenInner` (the bracketed inner's `match`), `chainRight` (the block after an operator), `chainOf` (the chain's grouping of its links), `appFrom` (a call's layout from what it reads: `keep`, the comment tests, the documents), `Expr.matchedParts`, `bodyDoc`, `Expr.callHug`, `Expr.opensBracket`, `Expr.lambdaHug` (the matches in `bodyAfter`), `defFrom` and `body.fst`, `body.snd` in `defDoc` (the final concat, and no pattern `let`). Each exists because a `match` written inside a rule is a function the proofs can't name, and a `Doc.concat` of stuck parts blocks `rewrite`. A rule that adds an arm to `bodyAfter` or `defDoc` (S6a) keeps these working if the new arm is in the named function.

### Findings for 18b

- **`MayFollow Bang` in `LexProofs.sw` is stricter than the lexer** and makes `printLexes1` unprovable for a prefix `!` before a name that starts with `i` (`!isSmall x`, `!inRange`): it asks the next character not to be `'i'`, where the lexer (`Lexer.sw`, `['!', 'i', 'n', next, ..]`) reads `!in` as `NotIn` only when a non-word character follows. It should say that: the rest doesn't start `in` followed by a non-word character.
- **`Lexical1` doesn't give `Decl.real`** (a token's text isn't layout): it says each word `lexesAs` a kind, and a lexer soundness lemma (a token's text starts with a character that isn't a space) is the missing step. `printedSpells` takes `real`.
- **The rules' joins are the rest of `printLexes1`.** `Fmt/PrintLexProofs.sw` (namespace `Fmt.PrintLexProofs`, 41 theorems) is the bridge from the engine to the lexer, for any document: `printedLexes` says that if `Joins (Follows kinds) doc (Plain None) (_ => True)` and every word of `doc` is `Printable kinds` (layout, a comment as rule N leaves it, or a token `Spells` as its kind), then `lex (Doc.print doc width)` is `Ok` of the leaves of the pieces' layout (`Laid`). `Follows kinds word next` is "not a comment, and the token the word is read as may be followed by `next`" (`MayFollow`); pieces of spaces after pieces of spaces are taken together (`pieceFold`), and the proofs are `followsOfPair` (a piece before the next one), `pairsFollowFold` and `piecesTextIsConcat`. `printedLexesExample` meets its hypotheses. What is left is, per rule, `Joins (Follows kinds) doc edge next` for the 25 or so functions of `Rules.sw` (the toy's `JoinProofs.sw` and `RuleJoinProofs.sw` are the pattern: triples `Passes doc pre post`; slice 1 adds `Choice`, `IfBroken`, `IdGroup`, `Displaced` and `CloserLine`), with the facts that carry the glue: a prefix operator glued to an operand that doesn't start `-` or `>` (`prefixGap`), a closer after a token, a closer joining a waiting comment's line (`CloseJoins`), `-x` and `f -x`; then `Printable` for the tree's words from `Lexical1` (a lexer lemma: a token's text is spelled as its kind and isn't layout or a comment), and the tree-side statement (`Spells` of the printed leaves against the tree's words, with commas) that ticket 17 reads.
- **18b's other statements.** `printedHangs` needs `printLays` with the columns (ticket 17's `hangs`), `printedKeeping` and `printedSettle1` the rule N side. `Doc.Proofs.Uniform`/`Marked` are done for every function slice 1 meets, so each of those starts from `elSpells`'s traversal.
## Slice 6a, the program (SW-3999)

Opus, 18 November 2026. The proof steps, on top of slices 1 to 5a, 4b and 4c: SW-3995's census put `RewriteRule` (799) and `Rewrite` (798) first among the kinds in a declaration kept out, and `Omega` (40) and `Iff` (25) among those alone in keeping one out.

### What is here

| Piece | Where | Rust counterpart |
|---|---|---|
| `rewriteDoc`, `ruleDocs`, `targetDocs`, `RewriteRule.el`: `rewrite rules at h then body` flat if it fits; else the body below at 2, and the rules one a line at 4 with `then` after the last when they don't fit on the `rewrite` line; without `then`, several rules as before one and a single rule joined by spaces; `<-` glued, a space after it; `at h` stays with the last rule | `src/Fmt/Rules.sw` | `rewrite`, `join` for `RewriteRule` |
| `ruleSetDoc`, `brokenRules`: `repeatedly [a, <- b]` as a comma bracket, flat or one rule a line at 2, never filled | `src/Fmt/Rules.sw` | `comma_bracket` for `RewriteRules` |
| `calcDoc`, `stepLines`, `CalcStep.el`: `calc e0` then each step on a line at 2 (a blank line above one kept); `_ R e := proof` with the proof as after a declaration's `:=`; a `calc` joins the `:=` line when its first line fits (a new arm in `bodyAfter`'s `lambda` choice, so it gets no `OneLineBelow`), goes below an arm's `=>`, and is a layout body for the header | `src/Fmt/Rules.sw` | `calc`, `calc_step`, `body_after`, `arm` |
| `cases then t`, `arithmetic [h]`, `algebra [h]` (and the keywords alone) | `src/Fmt/Rules.sw` | `join` |
| `↔` by `chain` with no level (nothing flattens into it) | `src/Fmt/Rules.sw` | `chain` for `Iff` |
| `within6a`, `Tok.within6a` (slice 4c's and `rewrite`, `cases`, `calc`, `arithmetic`, `algebra`, `↔`), `Decl.printed6a`, `SourceFile.printed6a`; `formatWithin` moves here from `Slice4c.sw` and refuses with `outside slice 6a` | `src/Fmt/Slice6a.sw` | |
| `Fmt.Twin --stage s6a`, `dev/fmt-twin s6a` | `src/Fmt/Twin.sw`, `dev/fmt-twin` | |
| Tests | `src/Fmt/Tests/Slice6a.sw` (6) | |

**The slice's edge.** `rewrite` is in every place an expression is (after `:=` and `=>`, in blocks, after another `rewrite`'s `then`, as a `calc` step's proof). Left out:

- **A gap Rust copies that the tree can't say:** the one after `<-` (`spacing.rs`'s `RewriteArrow` keeps the source's gap), printed as a space; no tracked `.sw` file has `<-` glued to its rule.
- **Comments on `<` or `-`** (a comment after `<-` makes Rust print an odd layout), and above a `calc` step's `:=`.
- **A `calc` whose first expression could hug** (`hugsNowhere`): Rust prints it with `no_hug`, a flag the `Around` doesn't carry; the slice takes only names, calls whose last argument is no tuple, list or record, operators, brackets and fields there.
- Pipes, sections, the unit and the rest as before.

### The gate [measured, Speedwell]

`dev/fmt-twin s6a --exe` with the interpreted twin (a slim copy with `Slice4a.sw` to `Slice4c.sw` and `Slice6a.sw`, without `Syntax/LexProofs.sw` and `Syntax/SettleProofs.sw`; a copied binary with `STITCHWORT_STD_DIR`; a fresh `FMT_TWIN_CACHE`, `--jobs 1`):

| Input | Declarations | Within slices 1 to 5a, 4b, 4c and 6a | Matched | Mismatched |
|---|---|---|---|---|
| `goldens` (132 files) | 644 | 420 | 420 | 0 |
| `repo --sample 300` (seed 1) | 5,870 | 3,940 | 3,940 | 0 |

The slices cover 67.1% of the sample's declarations; slices 1 to 5a, 4b and 4c cover 3,253 of the same 5,870 (55.4%; SW-3995 measured 55.8% of 5,947), so slice 6a adds 687. On the same runs `s1` stays 82 of 82 and 40 of 40, `s2` 230 of 230 and 436 of 436, `s3` 288 of 288 and 570 of 570, `s4a` 304 of 304 and 982 of 982, `s5a` 336 of 336 and 2,375 of 2,375, `s4b` 352 of 352 and 2,768 of 2,768, `s4c` 410 of 410 and 3,253 of 3,253. Hand files of rewrites flat and broken (with and without `then`, `at`, `repeatedly`, a long set), `then` chains ending in facts and `cases then`, a block after `then`, comments after a rule's comma, after `then` and above a rule, `calc` after `:=`, in an arm and as a block's value with a blank line and a comment between steps, and a long `↔`: `--stage text` identical to `stitchwort fmt -`.

What keeps the rest out [measured, as SW-3990's count]: of 1,930 declarations outside, 861 have no foreign kind (a shape the slice refuses), 629 two or more. With one foreign kind: `Unit` 157, `Section` 44, `Instance` 42, `Pipe` 37, `Chain` 26, `OperatorSection` 25, `ClauseLambda` 15, `Include` 15. Any foreign kind: `Binder` 234, `Unit` 229, `Pipe` 198, `Section` 198, `FunctionType` 137, `Fields` 132, `Field` 132, `RecordType` 121. Why the 861 shapes are refused wasn't looked into; they are now the largest group.

### For the proof lanes

- **The F1 tree is unchanged.**
- **Columns.** A broken `rewrite` puts its body at 2 from the `rewrite`'s line and later rules at 4; a broken `repeatedly` set puts its rules at 2 from that (6) and `]` at 4. `calc` steps are at 2 from the `calc`'s line, a step's broken proof at 2 from the step. A broken `↔` puts `↔` at 2. `cases then`, facts and `at h` never break between their tokens.
- **Rule N.** A `repeatedly` set's `[` and `]` are a bracket pair as a list's. A `calc` step is an item (a blank line above it kept), framed by its `_`; a rule is framed by its first token, as the `RewriteRule` node is in Rust's tree.
- **Edits to existing rules** are new arms only: `Expr.words`, `Expr.el`, `Expr.layoutBody`, `armDoc` and `bodyAfter`'s `lambda` match.

## Read-back, first part (SW-3969, Opus, 18 November 2026)

Ticket 17 of the proof plan: `hangs` in its final form, `blockOneLine`, and the item facts, in `Syntax/ReadBackProofs.sw`.

- **`hangs` (K3a) is `Fmt.hangs`** in `Fmt/Predicates.sw`, a step function (`HangState.step`) folded over a declaration's leaves after its `def`. It is the sketch's §1.4 with two clauses more, each found false of the sketch's form against the parser: the leaf after `->` doesn't start a line (the operand is read by `resultType` as a full expression, so `def d: A ->⏎    B⏎    C := x` reads as `A -> Block [B] C`, not `A -> B C`), and a `:` that starts a line is right of column 0 (`groupsOf` starts a declaration there). `Fmt.Twin --stage hangs` evaluates it, a line a declaration; `dev/hangs.py` checks the same rule. On seed 11's 400 generated files (250 formatted, 465 declarations) the two agree, and the only declarations that break it are 3 outside slice 1 (an `→` whose operand is a block).
- **`blockOneLine`**, both halves: `blockOneLine` (soundness, `Parse.ReadsAt`: a success read one line and gave its expression) and `runsBlockOneLine` (completeness, `Parse.RunsFrom`: it runs, reading exactly the line). The hypothesis `ends` is `continuesAt column rest = False`; `stepInBracket` and `stepAtTop` give it from `hangs` for an item's block and for the type's or body's.
- **Items from leaves**: `ItemsAt` is `itemsAfter`'s place (token before, index, depth, line indent); `itemsAppend` splits the items of a subtree's leaves from the rest, `pastIndex` makes a declaration's items numbered by their offsets (what `allow = Some offset` compares with `item.index`), `pastLast` gives `glued`/`afterOperand`'s token before, `pastDepth` keeps the depth across balanced leaves. `hangsAppend` splits `hangs` the same way.
- **Shape for the rest of readsBack1**: per parser function, `RunsFrom state (() => f self modes) (place.items leaves) rest value`, with `state.at.offset = place.index`, `hangsAfter` of the leaves from the state the context gives, and what `rest` starts with as the look-aheads need it. The node-by-node part waits for SW-3968, which splits every function on the path into named steps; `block`'s split here is SW-3968's, copied verbatim.
## Read-back, the whole tree (SW-4012, Opus, 18 November 2026)

Ticket 17c, in `Syntax/ReadBackTree.sw`, on SW-4004's `Syntax.ReadBackRuns`.

- **The relation is `Tree goal read rest value`**: `read`, followed by `rest`, is what the parser at `goal` should read as `value`. It is built from one `Prop` per rung of the parser's ladder (`AtomReads` with `BaseReads`' seven bases, `AppReads`, `UnaryReads`, `MulReads`/`AddReads`/`AppendReads` as `ChainReads`, `PipedReads`, `CmpReads`, `LogicAfterReads`, `EndReads`, `OperatorReads`, `InlineAt`, `BlockAt`, `FullReads`), each naming its children only through `sub`, the relation for the parser's calls to itself (bracket elements, arguments, a prefix's operand, the result after `->`). So no rung recurses on the tree; `Layer` picks the rung for the three levels slice 1 calls itself at (full, unary, argument), and `TreeN depth` nests it, `Tree` being some depth.
- **The knot is `runsTree`**: `Parse.runsRecursiveWith expressionRule Tree treeStep`. Each rung's runs lemma (`runsAtomTree` … `runsFullTree`) takes `SelfRuns sub self bound` and `read.length <= bound`, and shows each child shorter by arithmetic on the reads.
- **The result is `declarationTree`**, from the record `DeclarationTree` (17d's one target): the frame's four kinds, the type as `ResultReads Tree Modes.start` and the value as a `Tree` in the body's modes give `Parse.run` of the group as its `Definition`.
- **Building trees (for 17d)**: every rung is monotone in `sub` (`layerMono`), so `treeNRaise` lifts children to a common depth and `treeOfLayer` closes a node; `fullWord`/`treeWord` is the one-word case, and `itemsAround`/`declarationItems` cut a node's or a declaration's items through `ItemsAt`.
- **A line-start expression reads one way.** `expr` tests the item's index, not the parser's offset (`startsBlock modes item`, SW-4026), and a block's line allows the index of its first item (`nextIndex`), as Rust's `self.pos` does; in a declaration group indices are offsets, so the parser behaves as before. `FullReads` is the inline reading where no block starts or the block's where one does, and `BlockAt` reads its line in the modes that allow the item itself. (With offsets, SW-4013 proved `BlockAt` could hold of no word starting a line: the line modes allowed every offset, and a reading must hold from every state.)
- `InlinePlain` and `OperandEnds` (SW-4004) are now `Prop` records, so rungs can conjoin them.
- **Calls read back on one line** (SW-4026, `appLine`): a head atom and atomic arguments, each argument at the depth below the call. A list whose first element is `auto Name …` reads as an implicit binder, so the read-back assumes none (`Expr.autoFree1`; `typeFree` and `valueFree` on `readsBackLine`) until `shaped` excludes it (SW-4027). `-` and `!` need `lineKind` to admit `Minus` and `Bang`, and `Minus` is a section operator, so `groupLine` must then look at the last item before `)` rather than at every item.

## Read-back, signs and arrows (SW-4031, Opus, 18 November 2026)

Ticket 17f, in `Syntax/ReadBackLine.sw`. What reads back on one line now, and what the rest of `readsBack1` needs.

- **Signs.** `Spelt` has a `Prefix` case: the sign (`signKind`: `Minus`, `Bang`), its operand (no infix at the top, `Expr.unary`), and `negativeNumeral [sign, ..more] = (sign.kind == Minus && operand.numeral1)`: the glue the parser reads, so `-1` is one atom (`NumberBase`) exactly where the tree has `-` on a numeral. `unaryLine` reads any spelt expression at the unary level (a sign, its operand one level down; `-1` as an atom; anything else by `appAny`). `speltStarts` gives `leadKind` (an atom's first kind or a sign), `speltPlainStarts` the atom kinds for expressions that don't start with a sign (`signed`). `lineKind` and `exprKind` admit `Minus`, `Bang` and `Arrow`. `Minus` is no section operator (`Tok.isSectionOperator` excludes it; `Bang` is no operator at all), so signs needed nothing of `groupLine`; it was still reworked (below), for the binary operators.
- **Signs as arguments** (`f -x !b -1`): an argument is an atom, a bracket, or a sign on one (`Expr.signArg`), spaced as `argumentPrefix` asks (`argumentGlue`: the sign not glued to what precedes it, which ends an operand, and glued to its atom); `signArgLine` reads it as `SignBase`, or `NumberBase` for `-1`. A sign on a sign can't be an argument (`f -!x` doesn't parse: `!` is no `opensAtom`), nor a call's head but `-1` (`!x y` reads as `!(x y)`). Heads stay atoms: `-1 n` is not here.
- **Arrows** (`A -> B -> C`): `Spelt` has `Infix InfixArrow` with a left side that has no infix; `arrowLine` reads the left side by `unaryLine` (ended by `->`, `arrowUnaryEnds`), lifts it through the chains with no links, then `EndReads`' arrow with the right side by `fullLine` (`allowBraceOn` leaves the modes: no `{` starts a spelt expression). `inlineLine` picks `arrowLine` or `inlineUnary`.
- **`groupLine`** carries `pairPlain` under `beforeClosePlain`: only the item straight before the group's closer must be no section operator, which is all `rightOperator` reads. `rightPlain` takes `beforeClosePlain`; `rightLine` still gets it from `lineAll` (`lineBefore`), which stops working once `lineKind` admits a section operator (`+`): then it must come from `Spelt` (an operator is always followed by an operand).
- **`UnaryEnds`**: `unaryLine`, `appAny`, `appLine`, `argsLine` and `argEnds` ask only what ends a unary reading, so an operand followed by an operator uses the same lemmas (`arrowUnaryEnds` is the first such).
- **`typeFree`/`valueFree` from the tree**: `autoCallWithin1` (`within1` refuses the name `auto`, SW-4027) and `autoFreeWithin1`; `readsBackLineWithin` is `readsBackLine` with both discharged. `autoCall` looks down an infix's left spine, since `[auto Ord -> x]` reads as a binder too.

**`shaped` is too weak for read-back** [computed, `stitchwort eval` on hand-built trees, each `within1` and `shaped`]:

| Tree | Prints | Reads back as |
|---|---|---|
| `Infix - a (Infix - b c)` | `def d: A := a - b - c` | `(a - b) - c` |
| `App (Prefix ! x) [y]` | `def d: A := !x y` | `!(x y)` |
| `App f [Prefix - (Prefix - x)]` | `def d: A := f - -x` | `f - (-x)` |

`rightNeeds` lets a left-nesting operator's right operand sit at the operator's own level, `callArgument` lets a head be any prefix and an argument's prefix nest. The parser never builds these, so the end theorem is not false; but `readsBack1` can't take `shaped` as its shape fact. It needs the parser's own shape: a left-nesting chain's right operand one level up, a head an atom or `-` on a numeral, an argument's sign on an atom or bracket. Either `shaped` is tightened (and `parseShaped1` re-proved) or `readsBack1` takes a stricter fact proved of the parse.

**Glue is a printer fact nobody has stated.** `Spelt` now says how signs are glued (`negativeNumeral`, `argumentGlue`), and a binary `-` will need its right operand not glued (or `a -b` reads as a call). `printedTokens1` gives texts and kinds, `printedSpells` words; neither gives the items' `glued` or `afterOperand`. Step 4 needs a lemma on the printed items' spacing (`prefixGap` and the spaces around operators and between arguments): stated by SW-4070, "Printed spacing" below.

**What's left of `readsBack1`**: the binary operators (`* / %`, `+ -`, `++` as chains, comparisons, `&&`/`||` through `groupLogic`, and an arrow's left side at the logic level), each rung reading a chain by flattening the tree's spine, with the ends of each operand being the next operator (`UnaryEnds` and the chain rungs' `takesAhead`); multi-line declarations (step 3); and step 4's discharge: `Spelt` from `printedTokens1` and `printedSpells` plus the glue lemma, `lineAll`/`inLineAll`/`laterInLine` from the hang facts.

## Printed spacing (SW-4070, Opus, 18 November 2026)

What read-back's `Spelt` reads of the printed items' spacing, stated in `Fmt/OutputStatements.sw` and checked, not proved.

**The statement.** `Decl.spacing` gives one `Spacing` (`Free`, `Glued`, `Apart`) for each token of `decl.spelt.filter notComment`, commas included; `printedSpacing1` would be `spacingAdmits decl.spacing (items decl.leaves) = True` from `within1`, `shaped`, `settled` and `lexical`. It asks only what `Spelt` reads, plus what SW-4071's binary `-` will:

- a call argument's sign `Apart` from what precedes it, its operand's first token `Glued` (`argumentGlue`);
- `-` on a numeral: the numeral `Glued` (`negativeNumeral`); `-` on a numeral's call (`- 2 n`): `Apart`, which `prefixGap` spaces;
- an infix operator's right operand `Apart` from the operator, so `a - x` isn't read as the call `a -x` (an arrow's too: the same rule);
- the `Glued` demands only where no comment sits between the sign and its operand (`signQuiet`): a comment breaks the line.

`afterOperand` needs no printer fact: it is the token before's kind (`closesOperand`), which `printedTokens1` gives. `holdsOn` checks the statement on every example (`holdsOnSigns`, `holdsOnSignComments` added), and `spacingMatters` shows it isn't empty: `f - x`, `- 1`, `p -x` and `-2 n` fail it against the trees of `f -x`, `-1`, `p - x` and `- 2 n`. [computed, `byComputing`; and `formatWithin` on 15 sign and arrow cases, each as `stitchwort fmt` prints it]

**Found: `Spelt`'s prefix equation is false of a parsed source.** `def d: A := (- -- c\n  1)` prints as written: the comment breaks the line, so `1` isn't glued and `negativeNumeral` is `False`, while `Spelt` asks it to equal `operand.numeral1 = True`. The output still reads back (`readsBack` is `True`): the parser reads `-` then `1` as the same `Prefix`. So `Spelt`'s `Prefix` case should ask `negativeNumeral … = True → operand.numeral1 = True` (a glued numeral reads as one atom, which must be the tree's), and the converse only where the two readings differ: a call's head (`-1 n` against `- 1 n`, not in `Spelt` yet) or an argument (`argumentGlue` already). `unaryLine` would then split on `negativeNumeral` instead of on the operand. The same holds of an own-line comment above the numeral (`(-\n  -- o\n  2)`).

**Found: a comment on a glued sign breaks read-back, and the tree facts allow it** [computed, `stitchwort eval` on hand-built trees, each `within1`, `shaped`, `settled` and `lexical`, `readsBack` `False`]:

| Tree | Prints | Reads back as |
|---|---|---|
| `App f [Prefix (- -- c) x]` | `def d: A := f - -- c` / `    x` | `f - x` |
| `App (Prefix (- -- c) 1) [n]` | `def d: A := - -- c` / `    1 n` | `-(1 n)` |

The parser never builds them (a glued `-x` or `-1` has no room for a comment), and SW-4069's shape (an argument's sign on an atom or bracket, a head an atom or `-` on a numeral) still admits them. `readsBack1` needs a tree fact proved of the parse: an argument's sign, and a head's `-`, has no trailing comment and its operand's first token none above it (`signQuiet`).

**Why it isn't proved: no printer fact says where the spaces are.** `printedSpells` and `printedTokens1` give the words in order. `Joins` (Std.Doc) bounds which pieces may touch, by text, so it can't tell a binary `-` from a sign, and says nothing of what must touch. `Puts`/`Told` record a word's column only when it starts its line. The proof needs, in order:

1. Std.Doc: whether each word touches the piece before it. Either `Event` gains it (`eventsOf`: the piece before is no layout and the line isn't blank) and `Puts`, `Lays`, `Told` (`Spot` gains `touching`) and their printer theorems carry it, or a separate predicate in continuation style with its own printer theorem, as `Joins` has. Core std, so Opus.
2. The rules: an operand right after its sign with `prefixGap` empty and no comment touches it; `spaced`/`argumentDocs` and the chain's links put a space or a `Line` before each argument and right operand, so those never touch. Over slice 1's `Expr.el`, as `JoinProofs` does for `Joins`.
3. The lexer bridge: in `items` of `Decl.leaves`, a leaf laid right after a `Code` piece is glued (`endColumn` is `column + utf8Length` for a one-line text), one after a `Gap` or `Break` is not.
4. `printedSpacing1` from 1 to 3; then `Spelt`'s `Prefix` fix above, and `Spelt` of a printed expression for atoms, brackets, calls, signs and arrows (step 4's discharge).
## `shaped` is the parser's shape (SW-4069, Opus, 18 November 2026)

SW-4031's three trees that print as text parsing differently (`Infix - a (Infix - b c)`, `App (Prefix ! x) [y]`, `App f [Prefix - (Prefix - x)]`) are out of `shaped` now, and `parseShaped1` still holds (statement unchanged).

- **Rules, from the parser's code.** `rightNeeds`: an operator that nests to the left (`leftNeeds` is its own level: `+ -`, `* / %`) needs its right operand one rung up (16, 18), as `addExpr`/`mulExpr` read it; right-nesting ones (`++ && ||`, `->`) and comparisons are as before. A call's head is `Expr.callHead`: an atom, a bracket, or `-` (text `-`) on a numeral, since `unaryNext` hands `app` only a token that is no sign, or a `negativeNumeral`. An argument is `Expr.callArgument`: an atom or a bracket, or a sign on one, since `argumentPrefix` asks the next item to `opensAtom` (no sign does).
- **How the walk shows it.** `Nested` is now a `ReadsIn` (`GoalRead`), so the argument goal can say what it read: `ArgRead read expr` is an atom (`AtomParsed`) or, if `read` starts with a sign (`SignFirst`), a sign on one. An argument's sign is followed by an item that opens an atom, so the argument read after it is no sign (`argReadPlain`). Heads are walked from the mark `unaryNext` sees (`readsAppAt` with `readsAtomHeadPlain`, `readsAtomHeadNegative`, `readsAtomHeadNone`); `self` at `LevelApp` (rows, patterns: outside the slice) now gives `True`. Every other level's statement is as before.
- **Not in the tree facts yet: comments on a glued sign** (SW-4070's finding 2). `App f [Prefix (- -- c) x]` prints `f - -- c` with `x` on the next line and reads back as `f - x`; `App (Prefix (- -- c) 1) [n]` likewise reads back as `-(1 n)`. The parser never builds either: an argument's sign and a negative numeral need the next item `glued`, and a comment after the sign or above the operand puts it on a later line. Showing that needs an item invariant the walk lacks (`GoodItem` says only how a token is spelled): a glued item has no comment above it and its predecessor no trailing comment, from the lexer and rule N. Left as a follow-up.

### Step 1 done: `Std.Doc` touches (SW-4075, Opus, 18 November 2026)

A separate predicate, as `Joins` is, not a field of `Event`: `Event` is built in 143 places across `Places`, `Lays`, `Told` and the Fmt hang proofs, and none of them needs touching. All in `crates/elab/src/std/Doc/Touches.sw` (61 theorems, no open goals, no axioms).

- **What is recorded.** `touchesOf out` (pieces last first, as `eventsOf`): each printed word, in the order printed, as a `Touch` `{ word, touching }`, where `touching` says the piece straight before it is a word too (no space or `\n` between). `touchesWords`: its words are `wordsOf` of the pieces, so it lines up with `printedSpells`/`printedTokens1`.
- **The document side.** `Touches doc seam trace next`, continuation style like `Puts`, mode-blind like `Joins`. `Seam` is `Begun` (line start), `Along word` (pieces on the line, no comment waiting; `word`: the last is a word) or `Awaiting word comment` (a trailing comment waits; `word`: a closer here would touch). A chunk from `Along w` adds `{ text, w }` and leaves `Along True`; from `Begun`, `{ text, False }`. `Line`/fill separators: `Along False` (a space, or held after a comment) and `Begun` (a break), so the next word touches nothing either way. `SoftLine`: the seam unchanged, or `Begun`. `Nothing`, `Mark`, `BreakParent`, `Blank` and group edges leave the seam alone, so `a` then `b` with only those between touch. A trailing comment is listed where it is printed, when its line ends (`seam.ending`, appended at every break), so the list is in printed order; closers on its line come first, as in the text. `SuffixTouches` refuses a comment at a line start or a second one waiting (the printer would print them oddly; no rule builds either).
- **The run lemma.** `printTouches spec doc width (touches: Touches doc Begun [] (seam trace => spec (trace ++ seam.ending))): spec (touchesOf (printedPieces doc width).reverse)`, at every width. Printer side: `SeamSound` (indentation owed only at a line start, a line start has nothing on it, at most one comment waits, not at a line start, no spaces held without one) and `Printer.seam`/`Printer.touches` as functions of the printer; `stepTouches` per command, `readingTouches` over a reading with enough fuel. Witnesses: `printTouchesExample` (`f -x` from `[f, Line, -, Mark, x]`: `-` apart, `x` touching, at every width) and `closerTouchesExample` (`x) -- c`).
- **For step 2.** Rules prove `Touches (expr.el …) seam trace next` in triple style (as `HangLays` over `Lays`): an element starting from `Along w` adds its first token as `{ t, w }` and the rest as the element decides. A sign's operand after `prefixGap` empty: the operand's first token is written from `Along True` (or from `Awaiting` after a sign's trailing comment, which is `signQuiet`'s case). `spaced`/`argumentDocs` and chain links put a `Line` or `" "` before each argument and right operand: from `Along False` or `Begun`, so `touching = False`.
- **For step 3.** `pieceFold`/`Laid.lay` see the same pieces: a `Code` leaf's `glued` should be `touching` of its word, given `AllGood` (no empty piece; `""` is layout to `isLayout` but `Gap 0` to `pieceOf`). Comments are `Remark` pieces and have entries too (always `touching = False` when trailing); drop them by `notComment` to line up with `decl.spelt.filter notComment`.

### Steps 2 to 4: `printedSpacing1` against two open goals (SW-4076, Opus, 18 November 2026; closed by SW-4093, below)

`printedSpacing1` is stated in `Fmt/SpacingProofs.sw` with exactly the four hypotheses above and proved, relying on two named open goals: `appSteps` (calls) and `declSpacedTouches` (the definition's own document). `printedSpacing1Example` applies it to `def d: A := f -x`.

- **Step 3, proved** (`Fmt/GlueProofs.sw`, 23 theorems, audit clean). `printedGlued`: the `glued` of the items `Laid.lay` makes of the printed pieces is `codeTouching (touchesOf texts.reverse)` (each word's `touching`, comments dropped), given `CommentsEnd` (no code after a comment on its line, from `pairsEnd`) and `AllGood`. The fold keeps one invariant, `GlueTracks`: the glue flag is "the last text ends in a word, or is a comment", which avoids reasoning about UTF-8 lengths.
- **Step 4, proved from step 2's goal** (`printedSpacingOfTouches`): `printTouches` takes `SpacedTouches decl doc` (from `Begun`, `admitsGlue decl.spacing` of the touches) to the printed pieces, and `printedGlued` with `printedJoins` takes that to the items.
- **Step 2, the framework** (`Fmt/TouchSteps.sw`, 54 theorems, audit clean). `Steps doc pre spacing post`: from a seam meeting `pre`, the words the document adds are admitted by `spacing` (code words only) and it ends at a seam meeting `post`. Seam predicates: `Fits before first` (where a word spaced `first` may start; a comment may wait only if `before`), `Ends trails` (a comment waits only if the element ends with one), `Gapped` (after a `Line` or space), `Closed` (after a token). Combinators for every `Doc` form the rules use, `Fill` and `Choice` included.
- **Step 2, the rules** (`Fmt/TouchProofs.sw`). `ElSteps expr`: `expr.el around` from `Fits True first` adds `spacedFirst first (expr.spacing argument)` and ends at `Ends expr.trails`, given `within1`, `shaped`, `lexical`, `Joinable`, `argument → callArgument`, and `first` loose (admits a gap) or the first word quiet (no own-line comment, none waiting). Proved for tokens and their comments (a closer's `CloserLine` is what keeps a second comment from waiting), atoms, signs (`operandSpacing`'s three cases: apart after `prefixGap`'s space, glued under `signQuiet` with `callArgument` or a numeral, else free), brackets, tuples and lists (filled and broken) and infix chains (through `linkDocs`, mutually with `elSteps`). `elSteps` is the induction.
- **Left:** `appSteps`, whose route is `JoinProofs.appFromPasses` with the spacing carried per document (`spaced`, the `Fill` front, `HardLine` rest, the `Choice`'s three options and the hug, `IfBroken`); and `declSpacedTouches`, through `defFrom` and `bodyAfter`, which uses the call's hug too, so it comes after `appSteps`. Then `Spelt`'s `Prefix` fix and `Spelt` itself (step 4's discharge).

### Step 2 finished: `appSteps` and `declSpacedTouches` (SW-4093, Opus, 18 November 2026)

`printedSpacing1` now audits with no open goal: a slice 1 declaration's printed items are spaced as `Decl.spacing` says. No statement changed; 32 new theorems.

- **`Fmt/TouchSeq.sw`** (new, 20 theorems with the three fill lemmas moved from `TouchProofs`). `SeqSteps pre post docs spacings`: documents one after another, a space or line break between each two, each with its own spacing list beside it (two lists alike in length; a mismatch is `Void`), the first from `pre`, each later one from `Gapped True`, each but the last ending at `Ends True`. `spacedSteps`, `fillSteps`, `hardSteps` (each after a `HardLine`) and `seqSplit` (at `keep`, the back never empty) cover `appFrom`'s layouts; `appFromSteps` is every layout and `appFromHugSteps` the hug alone, as `JoinProofs.appFromPasses` and `appFromHugPasses`. `HugSteps` is `HugPasses`'s twin.
- **Calls** (`Fmt/TouchProofs.sw`). `argumentsSteps` follows `argumentDocs` with the spacings `initSpacings`/`lastSpacing` beside its documents; an argument starts from `Gapped True` with its own first spacing (`argumentStarts`: `Apart` for a sign, `Free` otherwise), so `spacing True` comes out as it is. A tuple or list as the last argument is `huggedBracket`, not its element: `lastArgumentSteps` steps it through `leadingSteps` and `bracketSteps` (its items by `allElSteps`, in the mutual block as `JoinProofs.lastArgumentPasses` does). `callHugSteps` gives a value's hug for the `:=` line.
- **The definition** (`Fmt/SpacingProofs.sw`): `plainDefSteps` follows `JoinProofs.plainDefPasses` (`def` and the name `spaced`, the `:`, `typedSteps`, the `:=`, then `bodySteps` for both of `IfBroken`'s forms: below, on the line, `OneLineBelow` through the new `TouchSteps.stepsOneLineBelow`, and the hug after a space); `spacedOfSteps` turns a triple from `Fits True Free` to a quiet seam into `SpacedTouches`.

## `Spelt`'s prefix clause and negative numeral heads (SW-4077, Opus, 18 November 2026)

- **The prefix clause is one direction now.** `Spelt`'s `Prefix` case asks `negativeNumeral [sign, ..more] = True → operand.numeral1 = True`, not the equation: SW-4070's finding 1, `def d: A := (- -- c⏎  1)`, where the comment leaves the `1` unglued and the parser reads a sign on a numeral. `unaryLine` and `signArgLine` split on `negativeNumeral` (`negativeMinus` gives the `-`). `readsBackLineWithin` keeps its name and shape and is stronger. Witnesses from the lexer's items: `commentMinusApart` (the old equation fails there), `commentSpeltExample`, `readsBackCommentExample` (the parse, by computing).
- **A call's head may be `-` on a numeral** (`def d: A := -1 n`, which every `PrintedGroup` fact admits and which made `printedSplit1` false as first stated). `Spelt`'s `App` case asks `headFits`: an atom or a bracket, or a prefix whose items the parser reads as a negative numeral, the one sign `unaryNext` hands to `app`. `signed` looks through a call to its head, so `unaryLine` reads such a call after its sign (`UnaryReads`' second branch) and `appLine` reads the head by `headLine` (`NumberBase`). Witness: `readsBackNegativeHeadExample`; `Fmt.PrefixHeadSplit` keeps the driver's tree and its `PrintedGroup` facts.
- **Toward `printedSplit1`** (`Fmt/SplitProofs.sw`, proved): `groupSpacing` (the group's items are spaced as `Decl.spacing` says: `items` reads glue from tokens alone, `gluedSameTokens`); `codeTextsOf` (an expression's spelling with comments filtered out is `codeTexts`, commas kept); `itemsChained` (each item's `afterOperand` is the kind of the one before).
- **An infix's kind matches its operator** (orchestrator's call, 19 November 2026). `within1` used to let `InfixBinary` and `InfixArrow` take any operator of the slice, so `Infix InfixBinary a "->" b` met every `PrintedGroup` fact, printed as `a -> b` and read back as an arrow, which made `printedSplit1` false (proved, then deleted with the fix). `within1` now asks `arrowText1` (`->` or `→`) of an `InfixArrow`'s operator and `binaryText1` (an operator of the slice that is no arrow) of an `InfixBinary`'s; `infixListed` gives back `operatorText1`. The parser builds arrows only from `Arrow` tokens and binary operators only from the others, so no parse is refused that wasn't before (read off `ParseWalk`, not proved: `within1` is the formatter's run-time test, so the theorems need no parser fact). `Spelt`'s `infixTok` and level facts then follow from `lexKind` of the operator's text.
- **Also proved toward it** (`Fmt/SplitProofs.sw`): `calm` keeps the spacing (`spacingCalm`, with `signQuietCalm`), the shape (`shapedCalm`) and the lexing (`lexicalCalm`), so `Spelt` can be shown of the calm tree from the printed tree's facts.
- **`printedSplit1` is proved** (19 November 2026), so `readsBackDecl1` and `readsBackFile1`'s read-back side have no open goal. `Fmt/SpeltSlots.sw`: `slots` of an expression (`Some word` per token, `None` per comma) and `SlotMatch` (a word's item carries it and `lexKind` of its text, a comma's item is `Comma`); `speltSlots`, the induction, gives `Spelt expr read` from the tree facts (`within1`, `shaped`, `lexical`, `commaFree`), the items filling the slots, `spacingAdmits (expr.spacing argument) read`, `Chained read` and the first item's `afterOperand`. No new hypothesis: `shaped`'s `signQuiet` (SW-4081) gives the quiet signs. `Fmt/GroupSlots.sw`: an expression's words are clean (`wordsClean`), its slots read as its code texts and words (`slotTexts`, `slotWords`), `calm` keeps the code texts (`codeTextsCalm`), no word lexes as a comma (`slotsCode`), so items with the slots' texts, kinds and words fill them (`slotsFromTexts`); `splitOfParts` splits the group at the `:` and `:=` and spells both parts; `printedSplitParts` gives its hypotheses from `PrintedGroup` (`printedTokens1`, `groupSpacing`, `calmShape`). `PrintedGroup`, `GroupSplit` and `Decl.calmAt` moved to `Fmt/GroupFacts.sw` so the proof can sit below `Fmt.TopReadBack`.
- **What is left on this path**: `edgeQuietOneLine1` (`Fmt.OneLineStatements`), the printing side's open goal, is the one open goal under the top theorems.

## One parse (SW-3964, proof plan ticket 13c)

`Lexed.tidied` parses once, from `Lexed.settledOnce` (`Settle.sw`): `withBareLastCommas` moves each last comma's comments as `withoutLastCommas` does (the move is `commaMoved`, shared by the two) and leaves the comma in with empty trivia, still starting its line if it did; then rule N. P2 drops the commas on the tree, so `Tidied.fourth` is `tidy` of the one parse. `parksComment` is gone. The search behind the choice is in the S1 sketch, §3.4's outcome: the sketch's way 2 with the comma off its line parses 54 in 3,000 generated files that Rust refuses; with the comma keeping its line start, refusals and trees are the old driver's on every file tried, and the text changes only where the old driver differed from Rust.

**Two families fixed** (tests in `Tests/Slice1.sw`): a closer's trailing comment that rule 1 left on a commentless comma starting the closer's line, which rule 2 then put above the closer (Rust keeps it on the closer; 24 of 2,481 generated files that parse); and K1's own case, where the closer, first on its line without its comma, sat at the item's column, the bare parse failed and the driver fell back to the plain parse unseen.

### The gate [measured, Speedwell]

Fresh cache, copied binary, slim copy without the proofs, `--jobs 1`: `passes` 132 of 132 (goldens) and 300 of 300 (repo `--sample 300`); `s1` to `s6a` every declaration within each slice matched on both (`s6a`: 420 of 420 and 4,043 of 4,043); `text` 54 of 132 and 40 of 300, as before the change (the rest are outside slice 6a). The probe over the goldens and every fourth tracked `.sw` file (943 that lex) found no file whose trees, comments or text the change moves.

### For the proof lanes

- `parse1` is `parseFile lexed.settledOnce`. On a text with no comma before a closer (every output) `settledOnce` is `settled`, since `withBareLastCommas` is the identity there.
- **`bareSettles`, proved (SW-4006, `Syntax/SettleBareProofs.sw`; up to line starts, SW-4183, `Syntax/SettleMarkProofs.sw`):** under `alphabet1` and `plain1`, `dropF [] lexed.settledOnce.leaves`, line starts ignored (`Leaf.unstarted`), is `lexed.settledBare.leaves`, and the two `end`s agree (`dropF` drops each comma directly before a closer after an item; no layout assumed). The line starts differ only at a closer after a last comma that starts its line: `settledBare` deletes the comma from the text, so the closer starts the line there, while the formatter keeps the comma and reads the closer as starting it. It is what ties `CommentsKept`, stated on `settledBare`, to the leaves the tree comes from. Rules 1 to 3 each commute with dropping the bare last commas (`home1Drop` with `walkDrop`, `commasDrop`, `arrowsDrop`); rule 4 does nothing in the alphabet and rule 5 works leaf by leaf. A `->` straight before a last comma would break rule 3, which `plain1` excludes. `settledOnceNone`: with no last comma (`noLast`, every printed text), `settledOnce = settled`.

## Slice 1 rules proofs, `printedHangs` (SW-4011, Opus, 18 November 2026)

Ticket 18d of the proof plan, in `Fmt/HangProofs.sw` (namespace `Fmt.HangProofs`).

### The framework, and why

- **Over the printer's trace, not a tree-shaped spec.** The toy formatter's `Events zone head expr` (EventProofs.sw) describes, per node, where each token may start, and a second proof takes that to the parser. Here `hangs` is already a step function, and `HangState.step` reads a leaf's column only when the leaf starts its line, which is exactly what `Doc.Proofs.Event` records (`start`). So the same fold runs over the trace (`hangOf`: `def` at column 0 first, then `HangState.step` on `eventLeaf`, comments and blank lines skipped), and the rules carry the fold's state in their triples. No second tree-shaped spec, and no port of the toy's 3,000 lines: what is ported is its `concatLays` and the shape of its word lemma (`writeOne`).
- **Triples like `JoinProofs`' `Passes`.** `HangLays kinds doc indent pre post`: from every place and fold satisfying `pre`, every way `doc` lays out (`Doc.Proofs.Lays`, continuation style) leaves a place and fold satisfying `post`. One combinator per `Doc` constructor; rules are lemmas about the named rule functions with the tree facts as parameters.
- **From `Std.Doc`:** `printLays` (a `Lays` from the start gives a laid trace that `Tucks` to the printed one) and nothing about columns beyond the `Place` itself; `tucksHang` shows the fold is the same over both orders (a tucked comment is skipped). `hangsPrinted` is the engine end: a triple for the declaration's document from `AtStart 0` to a fold that never broke gives `hangOf kinds (eventsOf (printedPieces doc width).reverse) ≠ Broke`.
- **An element folds as one token.** `ElHangs kinds doc indent before start`: from a seat (`Seated`: mid-line, at the start of a line at the indentation, or after a waiting comment only if `before`; no comment floor), with the fold at a state that allows the first word where `start` puts it (`Seat`: nothing in force right of the indentation, `Room` for the first word), the element ends after words (`Ended`) with the fold exactly as after one plain token there (`openedBy`). The brackets inside are opened and closed again, and every later line of an element starts right of its indentation, so the only thing an element does to the fold is what its first token does. The column facts come from the `Place`s alone: every line break lands at `floored carry X` with `X` at least the construct's indentation (and no floor at an element's edges), and a `CloserLine` at `closerAt`, at most the indentation.
- **Refinements made on the way.** `Ended state trails place` says whether a trailing comment waits (`Held` only if `trails`), so the next element knows whether it may start after one. `Seated` at a line start allows a shallower comment floor (`floored carry indent = indent`), as the comments above a token leave one; mid-line it needs nothing in force right of the line's column, so a comment break (`max indent (at + 2)`) is right of it. `PartHangs` is a later part of an element (an operand, an argument) starting where the previous element `Ended`.

### Where it got to (92 theorems, no open goals, no axioms)

Fold over the trace 6, triples and combinators 16, one per `Doc` constructor 23, words 6, `HangState` steps 8, elements 20 (plain leaf, displaced, framed, element then part, `elUnheld`), prefix operator 4 (`prefixHangs`), own-line comments 9 (`leadingHangs`: a token's comments above it, to the start of its line). `printedHangs` itself is not proved.

### Found

- **`Blank` after a line break can't be laid** (Std.Doc). `SepLays`/`SoftLays` give `AtStart` after a break, and `StartLays` turns `Broken` into `AtStart`; `BlankLays (AtStart …)` is `False`. So `Lays` is unprovable wherever the rules put a `Blank` after a `Line`/`SoftLine` break (`Word.leading`'s `[BreakParent, Blank]` for a bracket item after `brokenItems`' `Line`) or straight after `LineStart` (a blank line kept above a token's first own-line comment, when `around.item`). The printer does print that blank line (`Printer.blank`). Fixed by SW-4015 (below).
- **Fixed (SW-4015):** every line break after words now leaves `Broken` in `Lays` and `Puts`, as the printer is then (`newlinesAtEnd = 1`): `Line`, `SoftLine` and a fill's separator where they break, `LineStart` (and it keeps `Broken`), `LineStartHere` (likewise), `CloserLine`, `OneLineBelow`, and a `Displaced` element's comment break. `AtStart` is left for the start of the output, after a `Blank`, and a `HardLine` the document says has no `Blank` after it. `leadingHangs` now takes `(plainStart entry && note.blankBefore && around.item) = False`, which holds wherever the token is seated after words or right after a line break; `blankLeadHangs` lays `Word.leading`'s `[BreakParent, Blank]` from `Broken`. `commentKeepsFloor` is `Doc.commentKeepsFloor` (Print.sw, beside `floorAfter`), taking `text.startsWith "--"`; `Doc.Proofs.commentStarts` gives that from `IsComment`.
- **Closers on their own line need marks.** `CloserLine` lands at `closerAt`, the least marked indentation when that's at most the construct's. Showing that a closer then has room in the fold needs an invariant on the marks against the item blocks in force; not started.
- **No counterexample** to any `hangs` clause turned up in the rules read so far (none searched for by running `Fmt.Twin`).

### Still owed

- A token with comments above it as an element (`Word.leaf` with `leadStart`): needs `plainStep` at a line's own indentation rather than the construct's.
- `Word.leaf` for closers (`CloserLine`, marks), `Word.opening` (`Mark`), `closerNotes`/`laterCloserNotes`.
- `Expr.el` over every node: `parenDoc`/`parenInner`, `commaBracket`/`bracketContent`/`cells`/`brokenItems`, `huggedBracket`/`lastArgument`; `argumentDocs`/`appDocs`/`appFrom`/`spaced`; `chain`/`chainOf`/`chainLinks`/`chainRight`/`linkDocs` (`->` glue, `arrowsBare`).
- `bodyAfter`/`callHug`/`opensBracket`/`bodyDoc`, `headDocs`, `defDoc`/`defFrom` (the `:` and `:=` steps, the typed `Nest 4`), `doc1`.
- The bridge from the lexer's leaves (`Laid.lay` over `pieceFold`, columns in bytes) to `eventsOf`; then `printedHangs` from `hangsPrinted`, with the tree facts as hypotheses.

## Slice 1 rules proofs, `printedHangs` continued (SW-4016, Opus, 18 November 2026)

Ticket 18e, in `Fmt/HangProofs.sw` (rules) and the new `Fmt/PrintHangProofs.sw` (namespace `Fmt.PrintHangProofs`, the engine end). 60 theorems (with `closerLeafIsExample`) and 19 definitions, no open goals, no axioms; no statement of SW-4011's changed, no splits in `Rules.sw`.

### What is proved

- **Noted tokens (7).** `lineWordHangs` is `plainStep` at a line's own column rather than the construct's; `notedLeafHangs` and `notedPartHangs` take `Word.leaf` with comments above it as an element and as a later part, given `(plainStart entry && note.blankBefore && around.item) = False`.
- **Closers (25, with `CloserSeat`, `CloserFits`, `CloserFold`, `CloserToken`, `CloserEntry`, `CloserExit`, `Word.lone`, `LandsAt`, `NoteStart`/`NoteBroken`/`NoteWritten`).** `closerAtMost` (`closerAt ≤ indent`), `closerAtLower` and `breakKeepsCloser` (a line break deeper than the indentation keeps `closerAt`); `laterCloserNotesHang` for `laterCloserNotes`; `closerLineHangs` for `CloserLine`; `closerLeafHangs` for a closer's `Word.leaf` in all four cases (noted, lone, plain, trailed), taking the closer's seat and `CloserFits` as hypotheses.
- **Openers (4).** `openingHangs`: `Word.opening` (the `Mark`) from `Entered` to `Ended (openingBy state s)`.
- **The engine end (23, `PrintHangProofs`).** `hangsOfLays`: a declaration's document with a `HangLays` triple from `AtStart 0` to a fold that never broke, and `printedLexes`' hypotheses, lexes to leaves with `hangs = True`. The pieces: `tracks` (by induction over the printed texts, the last first: a token starts its line in `Laid.lay`'s layout exactly when its trace event does, and then at the same column, spaces in bytes as in characters; `stepColumn`: elsewhere `HangState.step` doesn't read the column; `stepTrivia`: it never reads trivia), `pieceFoldLay` (`pieceFold`'s merged gaps lay as the texts one at a time), `pairsEnd` (`printedJoins`' `Pairs` means no text after a comment on its line), `hangsOfFold` (the leaves' fold to `hangs`). So `printedHangs` is now exactly "a `HangLays` triple for `doc1`'s document", and what's left is all on the rules' side.

### Found

- **A blank line before a closer that trails a comment, after a last item that does too** (both printers). `def x: T := [\n  aaa, -- c\n  bbb -- e\n] -- d` formats with an empty line before `] -- d` (idempotent, and the output keeps `hangs`). The closer's `CloserLine` (it is `lone`) comes straight after `bracketContent`'s `SoftLine` break, and a `CloserLine` at a line start prints a newline more. `Lays` makes `CloserLine` need a mid-line place, so it is `False` there, and `CloserSeat`'s `Broken` case asks `lone = False`. Fix wanted in the rules or the printer (a `CloserLine` at a line start only moves the line), in both formatters (D3677: a shared bug). Related: when only the closer trails, its comment moves to the last item.
- **The marks invariant (owed).** `CloserFits` at a closer's seat needs (1) the least indentation `inForce` of the blocks outside the bracket to be at most `closerAt`, so the mark found by the bracket's key must be the opener's own, and (2) for parentheses, whose block may equal the indentation, `least ≤ block` and `marked < block`. Both need key reasoning: marks made inside an element have keys from `around.at` up. Options: a key floor and a "marks kept or lowered" post in `ElHangs`, or a generic `Std.Doc` lemma strengthening `Lays` by induction on `Doc` plus a per-rule walk of the keys. `framedBy` displaces `Held` entries, so an opener is never written at `Held`; comma brackets get (2) for free (block ≥ indentation + 2). Brackets then compose from `openingHangs`, the contents and `closerLeafHangs`.
- **Applications need a hoisted head seat (design question).** `appDocs`' `Nest 4 (Fill …)` puts a broken argument at a line start at the application's indentation + 4, but `Seated` at a line start asks `at = indent`. That condition carries `leadColumn`/`LineAt` for noted tokens (after own-line comments the `HardLine` lands at the floored indentation, not at `at`), so it can't simply be dropped; a seat variant for the head's arguments (and chains' `Nest 2` operators) is needed.
- **No counterexample** to a `hangs` clause: comments after `->` are moved by rule N and the output hangs.

### Still owed

- Brackets: `parenDoc`/`parenInner`, `commaBracket`/`bracketContent`/`cells`/`brokenItems`, `huggedBracket`/`lastArgument` (the marks invariant above).
- Applications and chains: `argumentDocs`/`appDocs`/`appFrom`/`spaced`, `chain`/`chainOf`/`chainLinks`/`chainRight`/`linkDocs` (the seat above).
- The declaration level: `bodyAfter`/`callHug`/`opensBracket`/`bodyDoc`, `headDocs`, `defDoc`/`defFrom`, `doc1`; then `printedHangs` is `hangsOfLays` applied to `doc1`'s triple.

## `parseCarries1`, first half (SW-4019, Opus, 18 November 2026)

`Syntax/ParseCarries.sw` (namespace `Syntax.ParseCarries`, 96 theorems, audit clean, no open goals) walks the
expression parser a second time, as `ParseWalk` does, for what `parseCarries1` needs: a tree in the slice has the
words of the items read for it, commas left out. `codeWords` moved here from `ParseSettledStatements`, which imports it.

### The spec and combinators

- `Carried read expr`: `expr.within1 = True → expr.words = itemWords read`, with `itemWords read = codeWords (read.map
  Item.leaf)`. A `Parse.ReadsIn GoodItems p Carried` per parser function; `NestedCarries self` at every goal.
- Words of items: `itemWordsAppend`, `itemWordsCode` / `itemWordsCons` (an item whose `(kind == Comma) = False`),
  `itemWordsComma`, `itemWordsAfterComma`; `codeAs` turns a kind known by `=` into its code fact.
- Lifting `ParseWalk`'s `Out` facts: `readsOut (outside.records modes)`, and `readsOutAfter before` where the spec
  is about `before ++ read` (after an opener, say). `readsNever` turns any `givesFail`-style fact into one at any spec
  (`readsFail`, `readsFailName`).
- Chaining: std's `Parse.readsThen` / `readsAtThen` / `readsDone`; `readsAfter0` (a look-ahead, then `j`);
  `readsAtBumpRead` (bump a known item, spec at `[item] ++ read`); `readsExpect` (`OneOf wanted`, and `oneOfWords`).
- Trees: `SameOrOut target` (kept, reading nothing, or outside the slice) with `sameOrOutThen` and `carriedSame`, for
  what follows an atom; `ItemsCarried` / `ListCarried` for comma lists and arguments; `carriedParen`, `carriedTuple`,
  `carriedList`, `carriedApp`, `carriedPrefix`, `carriedInfix`.
- Operator links: `LinkCarried`, `readsOperatorStep` (a round of `operatorLinks`), `carriedLeftNested`,
  `carriedRightNested`, `readsLeftChain`.

### What is proved

Atoms (words, `-`/`!` prefixes, negative numbers, `atomBase` by kind), what follows an atom (`suffixes`,
`atomRecord`, `atomAfter`, `atom`), parentheses and tuples, lists, comma lists, arguments and applications, `unary`,
`mul_expr`, `add_expr`, `append_expr`, and the knot: `bothExpressionAt` ties `ParseWalk`'s `GoalParsed` and
`Carried` in one `Parse.readsRecursiveWith` (the outside parsers' facts need `Nested`, so the two walks share the
recursion), and `carriesExpressionAt (ladder: LadderCarries): NestedCarries expressionAt`.

### For the second half (SW-4020)

- **Discharge `LadderCarries`**: for every `self` with `Nested self`, `NestedCarries self` and `Outside self`, a
  `Ladder self`: `expr`, `exprInline`, `logicLevel`, `cmpExpr` and `thenBody` carry their items. Then
  `carriesExpressionAt ladderOf` gives `expressionAt` at every goal, for the `def` frame and the file.
- **A level is proved as `readsMulExpr` and `readsAppendExpr` are**: `Parse.readsThen` down the function, each
  parser of the slice by its `reads…` lemma, each outside it by `readsOut` of its `Outside` field, folds by a
  `carried…` lemma; mirror `ParseWalk`'s `gives…` proof of the same function, replacing `Parse.givesThen` by
  `Parse.readsThen` (whose continuation also takes what was read) and `givesAfter0` by `readsAfter0`.
- **Two `Outside` fields are not `Out`** and can't be lifted: `pipeChains` (`result = value ∨ Out result`, which
  doesn't say that nothing was read when `result = value`) and `statementOthers` (`StatementOk`). `pipeChain` needs
  its own `Parse.ReadsIn … (SameOrOut value)` proof (it reads nothing unless a `|>` is ahead, and then gives an
  `InfixPipe`); a block's statements need theirs where `statementOther` can give an `ExprStatement`.
- **Things to check on the way**: `blockResult` gives a one-line block's value itself, so a block's spec is that
  line's; the logic chain's regrouping (`groupLogic`, `conjunctionOf`) must keep the words in order; the `def` frame's
  `def`, `:` and `:=` need `good` for their texts (`Decl.words` writes them back), and `(items group).map Item.leaf =
  group` for the file.
## Slice 1 rules proofs, `printedHangs`: seats and marks (SW-4030, Opus, 18 November 2026)

Ticket 18f. The design change first, then the rules' triples.

### The design

- **A seat column apart from the indentation.** `ElHangs kinds doc indent column before trails start`: `indent` is
  the indentation the element's document is laid at (its line breaks land there or deeper), `column` the column a
  seat at a line start is at. `Seated column` stays exact (`at = column`, no comment floor deeper), as before, so
  a token with comments above it still lands where `leadColumn` says; those lemmas take `column = indent`. `Seat`
  adds `column ≤ indent`. An application's head is the one element seated left of its indentation: `appDocs`' `Nest
  4 (Fill …)` lays it at the call's indentation + 4 while it starts where the call does. A chain's operators, and a
  call's arguments after a break, are seated where their line breaks land (`indent + 2`, `indent + 4`), so they
  are ordinary seats at a deeper indentation.
- **The marks invariant, kept out of `ElHangs`.** Marks matter only at a bracket's own closer, so rather than
  threading a carry relation through every element lemma, a frame lemma over `Lays` says that a document whose
  `Mark` and `CloserLine` keys are all at least `low` keeps every open mark with a key below `low`: found by its
  key, at the same `marked`, its `least` kept or lowered (`MarksKept`). The rules give the key floor: an element
  standing where `around.at` says uses keys from `around.at` up, and a bracket's contents start at its opener's
  `at + 1`. `CloserFits` then follows at the closer: (a) what is in force outside the bracket is at most the
  opener's line, which is the mark's `marked`, and at most the indentation; (b) for parentheses, whose inner may
  start a line at the indentation itself (after the opener's trailing comment), the line break there lowers the
  mark to that column, so the closer lands at the opener's line, left of it.

### What was proved

- `Fmt.MarkProofs` (17 theorems): `MarksKept`, the frame lemma `framed` and its helpers.
- `Fmt.BracketHangProofs` (46): the items of a filled or broken bracket (`fillCellsHang`, `brokenItemsHang`), the
  marked opener (`markedOpeningHangs`, `bracketOpening`), the closer with `CloserFits` from the opener's mark
  (`closerStep`, `closerFitsOf`), `bracketContentHangs` in all three layouts, `commaBracketHangs`, `listHangs`,
  `tupleHangs`, `parenHangs` and `parenElHangs` (opener ending no line with a comment), `huggedBracketIs` and
  `groupedBracketHangs`, `lastTuple` and `lastList`.
- `Fmt.AppHangProofs` (28): `spacedHangs`; arguments from their seats (`argHangs`, `lineArg`, `hardArg`), filled
  (`filledHangs`) and lined (`linedPart`); `Chained` and its cut (`chainedSplit`); `appFromHangs` over every layout
  (spaced, filled at 4, the choice of flattened, hug and broken with its rest at 2 or 4); `argumentDocsHang`,
  `appDocsIs`, `appDocsHangs` and `appElHangs`.
- `Fmt.ChainHangProofs` (9): a chain's runs (`runHangs`, `TailHangs`), `chainLinksForm` and `linkDocsForm` (a head at
  the chain's seat, then runs), `chainHangs` and `binaryChainHangs`, given what each operand and operator asks
  (`LinkFacts`, `PairFacts`).
- `CloserEntry` asks `CloserFits` only where the closer takes a line of its own (noted or lone), the only cases
  that read it: a weaker hypothesis, so stronger theorems.

### Findings

- `Lays` ignores groups, so it lays a broken bracket's `Line` after an item with a trailing comment flat, at the
  comment's `Held`. `brokenItems` passes `before = False` to every item after the first, so in that layout a node
  item would be written at the comment break without being displaced. The printer never prints it (the comment's
  `BreakParent` breaks the group), but the proofs must cover it: `ItemsHang` takes each item's `ElHangs` with the
  seat's `before` as the previous item's trails. Passing the previous item's trails as `before` in `brokenItems`
  would print the same and let the items' facts be uniform (CalmProofs and SpellProofs mention `brokenItems False
  arm False False`).
- `huggedBracket`'s opened form is not framed, so a bracket hugged after an argument that ends with a comment
  starts at the comment's `Held` with no displacement. `appDocsHangs` asks the hug to hang after the arguments
  before it (`ArgsHang`), which a bracket meets only when the argument before it ends with no comment.
- An element's trailing flag in these lemmas is what its parts say (`close.trails || trailsBeforeClose` for a
  bracket, `close.trails || inner.trails` for a paren, the last argument's for a call); `bracketTrails` and
  `tupleTrails` equate the bracket's with `Expr.trails`; the paren's and the call's equations are still owed.

### Owed

- A paren whose opener ends its line with a comment: the inner starts a line at `s ≥ at + 2` (`wordStart` at
  `Held`), so the bracket's block is `Some s`, and `CloserFits` (a) needs the mark lowered to at most `s` by that
  break, with `marked` (the opener's line, `at`) below it. That needs the first write after `Held` exposed through
  the inner's `ElHangs`, or a carry fact in its post.
- Chains of `->`: `PairFacts` asks the operator to hang as an element, which `->` doesn't, since after it the fold
  is glued rather than as after its first word; it needs its own run lemma, the operand starting mid-line and its
  `openedBy` ungluing the fold back to what it was. Slice 1 has no blocks or matches, so `chainRight` is always a
  space and the operand and the first operand opens no arms; `PairFacts` and `chainHangs` take those as facts.
- The declaration level (`bodyAfter`, `callHug`, `opensBracket`, `bodyDoc`, `headDocs`, `defDoc`, `defFrom`,
  `doc1`) and `printedHangs` through `hangsOfLays`. After `:=` the fold is `{ blocks = [], top = None, start = True }`
  (`HangState.step`'s `ColonEq`); the body below at 2 starts a line there, so `top` becomes `Some 2`, and on the
  `:=`'s line it starts none, so `top` stays `None` and its later lines are right of column 0. The header needs a
  lemma for a `:=` and a `:` leaf (both reset the fold with no bracket open) and the parameter groups' own.
- Equations from the lemmas' trailing flags to `Expr.trails` for a paren and a call (`bracketTrails` does it for
  brackets), and from the slice's facts (`within1`) to the hypotheses: `parenInner` writes the inner as it is, a
  chain's right operand is no block, its first opens no arms.

## `parseCarries1`, second half (SW-4020, Sonnet, 18 November 2026)

`parseCarries1` is proved (`Syntax.ParseSettledStatements`, from `Syntax.ParseCarriesFile.parseCarriesOf` and
`Syntax.ParseCarriesDecl.groupCarries`); hypotheses as stated: `FrameRest expressionAt`, `good` for every item of every
group, `parseFile lexed = Ok file` and `file.within1`. Three namespaces, audits clean:

- `Syntax.ParseCarriesLadder` (70 theorems): `ladderOf: LadderCarries` and `expressionAtCarries`. Pipelines (`pipeChain`
  as `SameOrOut value`), ranges, comparisons, `&&`/`||` (`carriedGroupLogic`: `groupLogic` keeps the words in order,
  given its fuel is more than the links), `->`, `expr_inline`, blocks (`BlockRead`: nothing, exactly one line, or more
  than one; `blockResult` of one line is that line's value), `expr`, `thenBody`. A block line from `statementOther`
  is proved outside the slice (`StatementOut`, copies of the four `StatementOk` proofs with the stronger conclusion).
- `Syntax.ParseCarriesFile` (8): `GroupCarries frame` (each declaration in a group carries the group's words),
  `parseGroupsCarried`, `parseCarriesOf`, `itemsLeaves` (`(items group).map Item.leaf = group`).
- `Syntax.ParseCarriesDecl` (about 45): `readsAtDeclaration` (a declaration group is read whole: `read = start.rest`),
  `readsAtDefinitionParts` (the header and body of a plain `def`), `readsAtLoopFirst` (a `loop` that gave `[]` stopped
  in its first round, from the mark it started at) and `readsAtParams`, which is how the `:` is known to be a `:`.

The def frame needed two facts the walks had no spec for, both found by reading the code: the header's `colon :=
fixedFrom()` bumps whatever follows the parameters, so its kind comes from the parameter loop having stopped at a `:`;
and `defKindOf` is `DefPlain` for any token but `theorem` and `instance`, so a `def` is known from the dispatch in
`declarationBody`. Neither is a statement change.
## Slice 1 rules proofs, `printedHangs` at the declaration (SW-4034, Opus, 18 November 2026)

Ticket 18g. `printedHangs` is proved (`Fmt.DeclHangProofs`): a slice 1 declaration's printed text, at any width,
lexes to leaves whose fold never breaks, from `within1`, `shaped`, `sound`, `lexical`, `doc1 = Some doc` and one
named hypothesis, `DeclHangs lexKind decl`. `DeclHangs` collects what is not yet derived from the tree facts: the
comment facts of the tokens (`TrailsComment` of `def`, the name, `:` and `:=`; no comments above the name, `:` and
`:=`), the name's `Plain` kind and `WordToken` spelling, the type's `ElHangs` at 4 and the value's `BodyLays` (below
at 2, and on the `:=`'s line with its hug when the `:=` trails nothing). `atomDecl` (`def d: A := b`) meets it.

### What was proved

- `Fmt.HeldParenProofs` (25): a paren whose opener trails a comment. The opener's place stays on its line; the
  inner's first break goes to `max indent (at + 2)`, and `HeldLowers` frames it so the mark is kept; `heldFits`
  computes `CloserFits` there. `parenAnyHangs`/`parenAnyElHangs` cover both cases of the opener.
- `CloserFold`'s `leftOf indent block` conjunct moved into `CloserSeat`'s `Broken` case, the only one that reads it
  (false when the inner's break lands at the indentation itself). Statement rearrangement; `closerLeafHangs` asks
  less.
- `Fmt.ChainHangProofs` (18): `->` chains. `RunOperator` is `HangsAt` or, for an operator that operates nothing
  after it, `GluesAt` (the glued state); `arrowRunHangs`, `arrowLeafGlues`, `arrowChainHangs`. `LinkFacts` and
  `PairFacts` ask `RunOperator` where they asked `HangsAt` (weaker).
- `Fmt.TrailsProofs` (6): `parenTrails` and `appTrails`, with `Coded` (some word read back is no closer) or a
  quiet opener; `atomCoded`.
- `Fmt.DeclHangProofs` (28): the head (`keywordHangs`, `headHangs`), the `:` and `:=` leaves to `topFrom`
  (`colonHangs`, `assignHangs`), the type at 4 after a space or below (`headerHangs`), `bodyAfter`'s forms
  (`bodyAfterHangs`, from `belowHangs`, `oneLineHangs`, `spaceDocHangs`, `plainChoiceHangs`, `openChoiceHangs`),
  `defFromHangs`, `defDocHangs`, `doc1Hangs`, `printedHangs`; `withinPlainBody` derives that a slice 1 value is no
  `match`, lambda or `calc`.

### Owed

- Each slice 1 expression's `ElHangs` from `within1` (an induction over atoms, parens, brackets, calls, chains and
  prefixes, assembling `ItemsHang`, `ArgsHang`, `LinkFacts`, `PairFacts`, `HeldLowers`, `Coded`, the arrow's bare
  token and `huggedBracket`'s opened form), to give the type's and value's facts in `DeclHangs`.
- The tokens' facts from `sound` and `shaped`: `TrailsComment` from `afterSound` (`commentText` to `IsComment`
  needs a `startsWith` to `toList` lemma), no comments above `:` and `:=` (or a lemma for their leading comments),
  and the name's `Plain` and `WordToken` from `nameWithin1`.
- Parameter groups: slice 1 has none, so `defDocHangs` takes `params = []`; later slices need `paramsHeader`.

## Slice 1 rules proofs, `DeclHangs` from the tree facts (SW-4045, Opus, 18 November 2026)

`printedHangs1Quiet` (`Fmt.DeclFactsProofs`) gives `hangs lexed.leaves = True` from `within1`, `shaped`, `sound`,
`lexical` and `DeclQuiet`: no own-line comments above the name, `:` or `:=`, and the type and value quiet
(`Expr.quiet`: every token with no comments above, none after, no kept blank line, and every call with an
argument). `printedHangs1` is the general form, taking `DeclElements` (the bare-token conjuncts, the type's
`ElHangs` and the value's `BodyLays`) in place of `DeclQuiet`; `printedHangs` is unchanged.

- **Trailing comments** (`trailsOfSound`): `afterSound` gives `commentText`, which gives `IsComment` through the
  characters (`dashed`: `--` then no line break; `withoutNewline`).
- **The name** (`nameFacts`): `Plain` and `WordToken` from `nameWithin1`'s `spellsOfText1 Lower`.
- **The induction** (`Fmt.ExprHangProofs.exprFacts`). Invariant, `ExprFacts expr`: for every `around`, the element
  hangs at any indentation and column after a waiting comment only where `around.before` says, trailing nothing
  (`HangsAt lexKind around.before False`); and for every level and `first`, its `LinkFacts` hold with no trailing
  comment. The second half is needed because a chain reads its operands through `linkDocs`, which flattens those
  of the same level. Mutual with `itemsHang`, `argsHang`, `lastHangs` and `hugFacts` (brackets' items, a call's
  arguments, the last argument as `huggedBracket` writes it).
- **Keys** (`Fmt.QuietKeyProofs.quietKeys`): a quiet expression's document has no `Mark` or `CloserLine` below
  any floor, by the same induction; `appFromKeys` covers every layout of a call. `quietExprFacts` is `exprFacts`
  with it.
- **Call hugs** (`quietHug`, from `appDocsHug`/`appFromHug`): the hug hangs as the function's element, from the
  front's spaced parts and the opened argument as a part, the same facts `appFromHangs` uses inside.

Findings (not consequences of the tree facts, so `DeclQuiet` names them):

- **Comments above `:`, `:=` and the name are slice 1.** Neither `shaped` nor `sound` rules them out, and the
  printer keeps them: `def x\n  -- c\n  : T := a` prints `def x\n  -- c\n  : T :=\n  a`; `def x: T\n  -- c\n  := a`
  prints as it stands; `def\n  -- c\n  x: T := a` prints `def\n  -- c\n  x: T :=\n  a`. `DeclHangs`' bare-token
  conjuncts fail for these. The fix is a noted form of `colonHangs`/`assignHangs` built from `leadingHangs`.
- **A noted element's start** (comment above a sub-expression's first token): `ElHangs` fixes the start function
  to `wordStart` (no start from a mid-line entry), but such a token starts its own line at `leadColumn` from any
  entry, so the post-state differs and `ElHangs` is false for it (`def x:\n  -- c\n  T := a`;
  `def x: T :=\n  -- c\n  a` likewise for the value). `notedLeafHangs` exists but nothing consumes it. The fix is a
  per-element start function (`leadStart` for noted elements) through every consumer lemma.
- **Items after a trailing comment** (`brokenItems` passes `before = False` to items after the first): a compound
  item after one that trails a comment is entered at the comment's break, held, but not displaced in a `Lays`
  layout, so `ItemsHang` likely fails for it; SW-4030 suggested passing the previous item's trails as `before`.

Owed: the three findings above, each of which widens `DeclQuiet` towards the four tree facts alone.

## Slice 1 trivia proofs, F2: what a word's document tells (SW-4049, Sonnet, 18 November 2026)

`Fmt/ToldWordProofs.sw` (namespace `Fmt.ToldWordProofs`), after SW-4056's `Doc.told` (`Std.Doc.Told`). Ticket F2 of
`docs/reviews/SW-4042-trivia-statement.md`: for every rule function that writes one word, what `doc.tell spot` says,
against the spot the rules enter it from. F3 (brackets, calls, chains, the declaration) composes these.

### The lemma shape

`Doc.tell doc spot` is a `Telling`: `said` (the entries) and `after` (where the printer may be after). Each rule
function gets one lemma, an equation between the document's `Telling` at a spot `spot` and a function of the word's
data:

```
theorem leafTell: (word.leaf around key).tell spot = word.leafTelling around spot   -- under word.sound
theorem openingTell: (word.opening around closer).tell spot = word.leafTelling around spot
theorem atomTell: ((Atom kind word).el around).tell spot = word.leafTelling around spot
theorem framedTell: (framedBy first around doc).tell spot
  = { said = first.toldLead around ++ (doc.tell (first.placedSpot around spot)).said, after = … }
theorem parenTell: (parenDoc open inner close around).tell spot
  = (open.leafTelling around spot).andThen ((parenInside …).andThen (close.leafTelling … (parenInside …).after))
theorem prefixTell / prefixElTell
```

- **Equations, not `ReadsAs`**: both `said` and `after` are stated, and `Telling.andThen` composes them
  (`tellAllAppend`, `concatTell`, `tellingQuietRight/Left`, `tellingAssoc` are here). F3's walk is `rewrite
  concatTell …, <each part's lemma>`, with the spot of each later part being the `after` of the one before. `spot` is
  universally quantified; the rules enter a word at `Spot.lineStart`, `Spot.afterWords.afterSep` (after `Line`,
  `SoftLine`, a fill separator) or after words, and `leafAtLineStart`, `leafAfterSep`, `leafAfterWords`,
  `leafAfterComment` give the result at each, with starts/follows as plain Booleans.
- **The word's reading is its printed word.** `Word.printed word around` is the word with the comments `Comments.kept`
  leaves (item flag from `around.item`, closer flag from its text), or, when the node's frame writes its own-line
  comments (`around.hoisted`), with none above and no blank line. `leafTelling`'s `said` is `(word.printed
  around).comments.toldAbove ++ [the word's own entry] ++ word.toldTrail`: for each note a `Gap` if flagged and `Said
  text True False`, then a `Gap` if the word's own blank line is flagged, the word, then `Said comment False True`.
  That is `stands`' `headedAs` word (its text, its comments above with their flags, its blank-line flag) and its
  trailing comment as `Said` on the same line. F3's link to `decl.stood` is a lemma per rule: the `calm` word at a
  position is `word.printed around` for the `around` the rule passes (`calm` writes `kept item closer`; the rules'
  `around.item` is `item`).
- **The word's own entry** is `Said text starts follows` read off the spot: at a line start `True False`; after a
  separator `True (!forced)`; after words `forced (!forced)`; after a waiting comment a closer with no line of its own
  slips in front of it (`False True`, `after` still the comment's) and anything else starts a line. `Word.forced` is
  "its comments or a kept blank line come first, or it is a closer taking a line of its own" (`ownsLine`).
- **Exactness** (`toldExact`, `leafTellingExact`, `exactAndThen`): no entry is `MaybeGap` or `Lost`. A `Blank` the
  rules write is always after a `LineStart`, `LineStartHere` or `HardLine`, so every `Gap` is exact (SW-4056).
- **Hypotheses**: `word.sound` (text not layout, notes are comments, SpellProofs' notion), and for `Word.opening`
  `isCloserText word.text = False`, so the opener has no line of its own.

### What is proved (count: see the file)

Notes and the word's pieces: `notesAboveTell`, `closerNotesTell`, `laterCloserNotesTell`, `closerLeadTell`,
`keptNone/Noted/Closer`, `leadingTell` (leading ends at a line start if it wrote anything), `pieceTell`, `bodyTell`.
Words: `leafTell` and its four spots, `openingTell`, `atomTell`, `toldLeadQuiet`. Frames and nodes: `framedTell`,
`parenInnerTell`, `parenTell`, `prefixTell`, `prefixElTell`. Exactness and witnesses (`toldItemBlank`,
`toldCloserOwnLine`, `toldCloserTucked`, …).

### For F3

- A node's `el` is `framedBy first around doc`: `framedTell` gives `first.toldLead around` then the document told from
  `first.placedSpot around spot`; inside, the first token is entered with `hoisted = True`, so its `toldLead` is empty.
- Composition: `(Doc.concat docs).tell spot = Doc.tellAll docs spot` (`concatTell`); a list split by `tellAllAppend`;
  a part's `Telling` is `andThen`ed; `rewrite` with the part's lemma at the exact spot.
- `Doc.tell` on `Group`, `Nest`, `Align` passes the spot unchanged; `Displaced` uses `spot.displaced`; the separators
  `afterSep`. `leafAfterSep` is the lemma for a first word after a `Line`.
- Not done here: items of a comma bracket (`itemAround`: `item = True` is where `leadSpot` reads `Gap`), `Fill`'s
  `plainItem` words, calls, chains, the declaration; `Doc.Proofs.laysTold` and `printTold` (SW-4056) carry the reading
  from the tell to the laid trace.

## Slice 1 trivia proofs, F3: what a declaration's document tells (SW-4050, Sonnet, 18 November 2026)

`Fmt/ToldDeclProofs.sw` (namespace `Fmt.ToldDeclProofs`, 135 theorems, `audit` clean), after F2's `Fmt.ToldWordProofs`.
Ticket F3 of `docs/reviews/SW-4042-trivia-statement.md`: brackets and items, calls, chains, the declaration. F4 (the
engine's tuck, then `printedStands1`) starts from `printedTold`.

### The statement

```
theorem printedTold ∀ (decl: Decl) (doc: Doc)
    (within: decl.within1 = True) (settled: decl.settled = True) (real: decl.real = True)
    (joins: DeclJoins lexKind decl) (shows: decl.doc1 = Some doc):
    Refines (doc.told Spot.lineStart) decl.shape ∧ dropCommas decl.shape = wordsShape decl.stood
```

- `decl.shape` is a `List Told`: for each token of the declaration in order, its own-line comments (a `Gap` above a comment
  or a kept blank line, `Said text True False` for each comment, `Gap` for a blank line below them), the word
  `Said text True flag`, its trailing comment `Said comment False True`; and `Said "," True True` between a bracket's
  items. The `def`'s own-line comments are left out, as in `decl.stood`.
- `wordsShape` is the same for a word list, and `dropCommas` removes the bare commas, so the second conjunct is "the
  shape is `decl.stood`'s words with bare commas". Every comma entry is a `Said "," True True` the rules write after an
  item that has a successor; no word of the tree has that text (`Expr.spelled`).
- `Refines told shape`: same length, each blank line a blank line, each word the same text, and the told flags allow no
  more than the shape's. So no entry is `MaybeGap` or `Lost` (exactness is part of `Refines`).
- **The flag**: `flag = !(isCloserText word.text && word.trails)`: a closer that holds a comment is `Said text True
  False`, so its told entry never follows words (`stands`' clause 3); every other word is `True True`, left to the
  layout: after a `Line` or `SoftLine` the same word may start a line or follow words, so no stronger statement holds of
  all layouts. What follows a waiting comment (a closer that slips in front of it, a comma) is the engine's tuck (F4),
  not told here.
- Hypotheses: `settled` gives `homedBack decl.words.reverse`; `real` and `settled` give `decl.sound` (as
  `printedSpellsSettled`); `DeclJoins` gives that no token is a comma or closer but the brackets' closers
  (`declTexts`). **No quiet-only hypothesis was needed** (no `DeclQuiet`): the `Choice`s and `IfBroken`s tell the same
  shape in every option (`mergeRefines`), and `homedBack` is what the rules' `around.before` for a closer reads.

### How it is proved

- `Is doc shape := ∀ spot, Refines (doc.tell spot).said shape`: the reading's entries do not depend on the spot (a word
  is one `Said`, only its flags vary), so every rule's lemma holds from any spot and the spots never have to be tracked.
  `Is` composes (`isCons`, `isAppend`, `isConcat`, `isFill`, `isChoice`, `isIfBroken`, ...) as `Spells` does.
- `Word.homes word around`: a closer that holds a comment is not hoisted and has comments above it or follows code ending
  with a comment (`around.before`); `forcedOfHomes` gives `Word.forced` (a line of its own), `leafShape` and
  `openingShape` follow from F2's `leafTell`/`openingTell`. `closeHomes` derives `homes` for a bracket's closer from
  `homedBack ([close, ..xs] ++ prior)`: `around.before` of a closer is computed from its siblings, never inherited
  (`trailsBackCoded`, `trailsBeforeCloseIs`), so no invariant relates `around.before` to the words before the node
  (an item after a comma gets `before = False`, whatever the code before ends with, and only its closers matter).
- `elShape expr around prior`: any `within1` expression's element tells `expr.shape around.item around.hoisted`, given
  `homedBack (expr.words.reverse ++ prior)` (`prior`: the words before it, newest first); the walk is `SpellProofs`'
  (`elSpells`) with `Is` in place of `Spells`: `framedShape` (the node's frame tells the first token's own-line comments,
  `shapeLead`), `parenShape`, `prefixShape`, `bracketContentShape` (`bracketFromShape`, `cellsShape` for the `Fill`'s
  `plainItem` cells, `brokenItemsShape`), `appDocsShape` (`appFromShape`, `frontRestShape`, `argumentDocsShape`,
  `huggedBracketShape`), `chainLinksShape`/`linkDocsShape`, `bodyAfterShape`, `plainDefShape`, `doc1Shape`.
- `declStood`/`shapeStood`: the shape without bare commas is `calm`'s words, node by node.

### Counts

135 theorems, 35 defs. Foundations (`Refines`, merge, append): 6; words and leaves (`leafShape`, `openingShape`,
`homes`): 11; shapes and frames: 7; `Is` combinators: 24; homedBack/coded lemmas: 6; items and brackets: 9; calls: 19;
chains: 6; `elShape` and its helpers: 3; the body: 7; the declaration: 9; stood and texts: 24; witnesses: 4 (sections as in the file; counts are of `theorem` lines).

### Not done / for F4

- The tuck: `Tucks` turning a laid reading into `stands` of the printed leaves (flags of closers and commas after a
  waiting comment are not in `decl.shape`; F4 reads them from the engine).
- The file loop's blank lines and the `def`'s own-line comments are outside `decl.shape`, as in `decl.stood`.

## Slice 1 `printedFinish1`: a document's last word (SW-4066, Opus, 18 November 2026)

### The predicate (sketch, before the proofs)

The end-side mirror of `Std.Doc`'s `Leads`, in `Doc/Ends.sw`:

- `Silent doc`: writes nothing and breaks no line: `Nothing`, `BreakParent`, `Mark`, `LineSuffix` (it only leaves a
  comment waiting), and a `Concat` of silent docs.
- `Finishes last doc`: whatever the layout, the last thing `doc` writes is a chunk or closer whose text `last` holds of,
  and after it only silent docs. A chunk or closer by `last`; a `Concat` whose last doc that isn't silent ends; a
  nest, align, group, flatten, displaced or one-line-below of a doc that ends; an `IfBroken` whose branches both
  end; a `Fill` whose last item ends; a `Choice` whose options all end (and there is one).
- On the work list: `StackFinishes last stack`, some command ends and every one after it is silent. A step only changes
  the front of the work list, so commands after the one that ends stay as they are.
- The run lemma (`readingFinishes`): from `StackFinishes` (or, once the last word is written, a printer whose last piece is
  that word, not at a line start, with only silent commands left), every reading with the budget ends with the
  printer's last piece that word, on a line it started. Nothing after it but the waiting trailing comments, each
  written after one space when the output is flushed (`printedFinishes`): the printed pieces are
  `front ++ [word, " ", c1, " ", c2, …]`, with every `c` a trailing comment of the document (`Marked`, via
  `stepQuiet`), so never `"\n"`.

At most one trailing comment is not `Finishes`' business: `PairsFollow` (from `declPiecesOk`) says a comment is
followed only by a line break, so `" ", c2` can't follow `c1`. For slice 1 the induction (`elFinishes` in
`FileLexProofs`) shows each element ends with its last token (a leaf's `piece`, its trailing comment silent after
it), using the tree's `Joinable` facts for the token being no layout and no comment.

### What was proved

- `Std.Doc` (`Doc/Ends.sw`), 29 theorems: `Silent`, `Finishes` (not `Ends`, a name `FileLexProofs` already uses for
  layouts) and their list and work-list forms; `stepFront` (a step only changes the front of the work list),
  `cmdFinishes`, `silentStep`, `readingFinishes`, `readingQuiet` (`stepQuiet` over a reading), `flushTopped`,
  `printedFinishes`; and the building lemmas `finishesConcat`, `finishesAppend`, `finishesLastAppend`,
  `joinedFinishes`, `finishesOfLast`.
- `Fmt.FinishProofs` (new file), 31 theorems: `elFinishes` by induction over slice 1's expressions (mutual with
  `appFinishes`, `argumentsFinish`, `lastArgumentFinishes`, `chainLinksFinish`, `linkDocsFinish`), `bodyFinishes`
  over `bodyAfter`'s options, `defFinishes`. The last word is `Final`: no layout and no comment, from `Joinable`'s
  `WordJoins`/`CloserJoins`.
- `Fmt.FileLexProofs`: `printedFinish1` closed (statement unchanged), with `pieceFoldCode`, `spacedFold`,
  `tailOfComments` (`PairsFollow` rules out a second trailing comment) and `commentShape` (with an example, so the
  audit's search isn't vacuous). `printedSeam1`, `declsLay`, `fileLaid` and `printedFileLexes1` now have no open goal
  under them: `audit Fmt.FileLexProofs` 56 theorems, all pass.

At most one trailing comment comes from `PairsFollow`, not from the tree's `before` flags (a closer after a comment
with a comment of its own takes its own line, S39): that rule is what makes `PairsFollow` hold, so the proof doesn't
repeat it.
## Slice 1 trivia proofs, F4: the engine end and `printedStands1` (SW-4051, Opus, 18 November 2026)

`Fmt/StandsProofs.sw` (namespace `Fmt.StandsProofs`, 62 theorems, `audit` clean). `printedStands1` is proved there and
no longer an open goal in `Fmt.TriviaStatements`, which keeps a pointer.

### The statement, as proved

```
theorem printedStands1 ∀ (decl: Decl)
    (within: decl.within1 = True) (shaped: decl.shaped = True)
    (settled: decl.settled = True) (lexical: decl.lexical = True)
    (plain: decl.unreturned = True)
    (facts: DeclHangs lexKind decl):
    decl.stands = True
```

Two hypotheses beyond the four tree facts:

- `unreturned`: no comment of the declaration ends in a carriage return. Without it the statement is false
  (`returnedFalls`: `def d: A := b -- c\r`, built by hand, meets the four facts but the lexer's `withoutReturn` takes
  the return off, so the leaf's comment is not the tree's). The parser never builds such a tree; SW-4061's
  `SourceFile.unreturned` is the file-level cousin, for the file loop's comments only.
- `DeclHangs lexKind decl`: what `printedHangs` takes, from which `doc1Hangs` gives the document's `Lays`, which
  `printTold` needs. Chosen as the most general of the three (`DeclQuiet` → `DeclElements` → `DeclHangs`, by
  `quietElements` and `declHangsOf`); the orchestrator may prefer `DeclQuiet` for a statement with no element facts.

### How it is proved

- The lexer as a fold over printed events (`Hearing`, `hearAll`); `laidHears`: `Laid.lay` over the printed pieces
  gives the same leaves, pending comments and blank flags (`Hears`), given `CommentsEnd`.
- `Heard owed bits views` mirrors `stands`; `heardStands` turns it into `stands owed (bitsWords bits) leaves = True`.
- `Bit` (a word, or a bare comma): `Expr.bits`/`Decl.bits` are written as `Expr.shape`, so `shapeBits` and
  `declShapeBits` hold with no hypotheses; `exprBits`/`declBits` give `bitsWords decl.bits = decl.stood` and
  `BitsFine lexKind` (each token reads back as its kind, no comment, no comma) from `within1`, `sound`, `lexical`,
  `unreturned`.
- The tuck: `bitsHeard` walks the bits against `Tucks`'s stretches (`HeardFrom`, quantified over the hearing so far):
  a waiting trailing comment is printed after the closers and commas that follow it, and the hearing hands it to the
  last of them, as `stands` says. `keptFront` splits the stretches at a word's own events.
- `refinesReads`: `Refines told shape` and `ReadsAs told events` give `ReadsAs shape events`.
- `standsOfDoc` assembles: `doc1Hangs` → `printTold` → `printedTold`'s refinement → `bitsHeard` → `heardStands`, with
  the leaves from `leavesHeard` (`pieceFoldLay`, `laidOfFold`) and `CommentsEnd` from `pairsEnd`.

### Not done

- A witness that `printedStands1` applies to a declaration with comments: `atomDeclStands` has none, since a
  `DeclHangs` proof for a commented declaration is long by hand.

## Slice 1 rules proofs, noted header leaves (SW-4057, Sonnet, 18 November 2026)

`DeclQuiet` no longer excludes comments above the name, the `:` and the `:=` (SW-4045 finding 1); it is now `header.result.quiet = True ∧ value.quiet = True`. `printedHangs1Quiet` keeps its name and conclusion with the smaller hypothesis. `Fmt.DeclHangProofs` 35 theorems (7 new), `Fmt.DeclFactsProofs` 24 (6 new), audits clean.

- **`notedStepHangs`** (and `lineStepHangs`): a header token with own-line comments above it, after words: `leadingHangs` to the start of its line, the token there as one step of the fold (a hypothesis, `step`, from `state` to `final`), then its trailing comment. `colonNotedHangs` (`stepColon`, to `topFrom`) and `assignNotedHangs` (`stepAssign`, from `topState top`) apply it; `colonAnyHangs` and `assignAnyHangs` split on the comments (`notesCases`) and use the bare `colonHangs`/`assignHangs` otherwise. The room for the token comes from `Ended`'s `inForce ≤ at` alone: the comment break lands at `max indent (at + 2)`.
- **The name** (`namePartHangs`): bare (`elPart` of `plainLeafHangs`) or noted (`notedPartHangs`); `headHangs` takes `NotesComment name.comments.above` in place of `name.comments.above = []`.
- **`DeclHangs`** asks `NotesComment` of the three comment lists instead of `= []`; **`DeclElements`** loses those three conjuncts, since `declHangsOf` derives them from `sound` (`notesOfWord`, from `commentIs`). So `printedHangs1` is stronger too.
- Witnesses: `colonNotedDecl` (`def d⏎  -- c⏎  : A := b`) and `assignNotedDecl` (`def d: A⏎  -- c⏎  := b`) meet `DeclQuiet`, `within1`, `shaped`, `sound` and `lexical` (`colonNotedMeets`, `assignNotedMeets`).
- No comment above the name witness: not tried (`nameWithin1` may exclude one; `namePartHangs` covers it anyway).
- Still owed from SW-4045: a noted element's start inside the type and the value (SW-4058), and items after a trailing comment.
## Slice 1 rules proofs, noted starts of the type and the value (SW-4058, Opus, 18 November 2026)

`DeclQuiet` no longer excludes own-line comments above the type's or the value's first token (SW-4045 finding 2,
`def x:\n  -- c\n  T := a`): it is now `header.result.leadQuiet = True ∧ value.leadQuiet = True`, quiet but for
comments above the first token (`Fmt.ExprHangProofs.Expr.leadQuiet`). `printedHangs1Quiet` and `printedHangs1` keep
their names and conclusions; `quietElements` takes `sound` too (for the comments' `NotesComment`).

- **Start per element** (`Fmt.HangProofs.startFor noted`: `leadStart` if noted, else `wordStart`; they agree at a line
  start). `DeclHangs`, `DeclElements` and `BodyLays` give the type's and the value's `ElHangs` at
  `startFor header.result.noted` / `startFor value.noted`; `BodyLays`' on-the-line part asks `value.noted = False`
  too, since `bodyAfter` lays a noted value only below. `startTopHangs`, `midTopHangs`, `belowTopHangs`,
  `headerHangs`, `belowHangs` take `noted`; mid-line, a noted type starts the comment break's column
  (`Nat.max indent (at + 2)`, right of column 0).
- **A noted node** (`notedFramedHangs`): `framedBy` writes the comments (`leadingHangs`, to the start of the line at
  `leadColumn`) and displaces the node there; `linedDisplaced` lays it from that line start using the node's
  *hoisted* facts (`Doc.concat [Doc.concat [], Displaced doc]`, which `expr.el { around | hoisted = True }` is for a
  noted first token), laid at that column. `Fmt.DeclFactsProofs.notedNodeHangs` packages it per node kind;
  `leadElHangs` covers names and numerals (`notedLeafHangs`) and the six node kinds.
- **The induction** (`leadFacts`, replacing `exprFacts`' body; `exprFacts` is now its quiet case): for
  `leadQuiet` expressions, `LeadFacts` is `ExprFacts` restricted to the places where the element writes no comments
  above its first token (`Expr.bareAt`: hoisted, or none). The call's head and the chain's first operand share the
  first token and are laid hoisted; everything else is quiet.
- Witnesses: `typeNotedDecl` (`def d:\n  -- c\n  F A := b`) and `valueNotedDecl` (`def d: A :=\n  -- c\n  f b`)
  meet the four tree facts and `DeclQuiet` (`typeNotedMeets`, `valueNotedMeets`). The printer (Rust `stitchwort fmt`
  and `formatWithin`, test "comments above the type's or the value's first token put it on a line of its own")
  prints `def d:\n    -- c\n    F A :=\n  b`, which hangs as the proofs say: the type starts column 4 after the
  comment, its later lines right of it.

What `DeclQuiet` still names (open, SW-4058's remainder): inside the type and the value,

- **comments above a later token** (an argument, an item, a chain's operand or operator, a closer): the rule-level
  lemmas take their sub-elements' `ElHangs` (`Hangs`, `ItemsHang`, `LinkFacts`) at `wordStart`. Arguments and chain
  operands after the first are parts, where the start doesn't change the fold (`openedQuiet`), so `elPart` over
  `startFor` (with `endedLead`) should carry them; items start their block (`state.start`), so `ItemsHang` needs the
  item's own start, and a noted item at a plain line start needs its first comment's blank line ruled out
  (`notedLeafHangs`' `quiet`). The induction would then carry `leadElHangs`' noted case for non-hoisted places.
- **trailing comments anywhere** (`ExprFacts` trails `False`), and the items after one (SW-4045 finding 3);
- **kept blank lines** (`Comments.blankBefore`), and calls with no argument (outside what the parser reads).

## Parser proofs 16f: `FrameRest`'s last field (SW-4017, Sonnet, 18 November 2026)

`FrameRest.others`, the assumption that `declarationOther` gives a declaration outside slice 1, is proved:
`Syntax.ParseWalkOthers` (63 theorems; `givesDeclarationOther`, `frameRest: FrameRest expressionAt`, and
`parseCarriesSourceProved` / `parseSettledSourceProved`, the two source theorems without the frame hypothesis). Every
parser it reaches (type, interface, ability, test, rules, export, opaque, instance) is walked as `Gives` facts of the
parts (binders, constructors, fields, operations, the expression parser through `givesExpressionAt`); the result is
outside slice 1 by construction (not a `Definition`), or, for `export` and `opaque`, by the header keeping the keyword
(`givesDefinitionPartsAny` now says so; `headerOutOfExport`, `headerOutOfOpaque`).

- `FrameRest.others` as it stood was false: `declarationOther modes attributes (Some KwInstance)` parsed a
  `definition`, which reads its kind from the next token again, and `seen` isn't tied to the parser's position, so with
  `def x: Nat := 1` next it gave a plain definition, within slice 1. `instanceDecl` now fails unless the header's kind
  is `DefInstance` (it always is, when `seen` is what the next token is), and `givesInstanceOf` uses that.
- `DeclParser`'s data, ability, test, rules, export and opaque parsers are split into named steps, one effectful
  condition each (`dataIndexAt`, `constructorBraced`, `exportAfter` ...), as the other walks need; behaviour is unchanged.
- `FrameRest` and the theorems that take it keep their statements; `frameRest` is what to pass.

## Read-back, `&&` and `||` on one line (SW-4090, Opus, 18 November 2026)

Ticket 17g-ii, in `Syntax/ReadBackLine.sw`, after SW-4071's other binary operators. `binaryTok`, `lineKind` and `exprKind` admit `AndAnd` and `OrOr`, so `Spelt`'s one `Infix` case takes them with no new case, and `readsBackLineWithin` reads them with its statement unchanged.

- **Flattening.** The parser reads a comparison, then flat `&&`/`||` links (`logicLinks`), and `groupLogic` regroups them: `&&` within each disjunct, `||` between, both to the right. `orFlat` walks the `||` spine, `conjFlat` each conjunction's `&&` spine with the links after it as an accumulator (`ConjFlat`), so `conjunctionOf` provably takes exactly the `&&` run (`conjunctionAnd`, `conjunctionStop`) and `groupLogic` with any fuel above the link count gives the tree back (`LogicSplit`). Both are on `Spelt` alone, not on reads.
- **Outside the recursion.** `logicLinks` (each link's comparison) and `logicOperator` (all of `OperatorReads`) take `cmpLine` as a hypothesis (`CmpLineAt`); only `operatorLine` is in the recursion, passing `cmpLine` at its depth as a lambda. So no large `∃` is taken apart inside the mutual block, which is what ran out of resources in SW-4071. `operatorLine` now reads every level from `||` up this way (a comparison is a chain with no links).

## Read-back, `auto` where the parser allows it (SW-4128, Opus, 19 November 2026)

Lane A of docs/reviews/SW-4166-carried-walk-plan.md. Lane L's `textSpells1` takes the name `auto`, so `within1` no longer keeps `[auto Ord]` out, and read-back's `Expr.autoFree1` (no list at any depth starts with an `auto` call) was false of slice 1 trees such as `f [auto Ord]`, which the parser reads as a list.

- **`Syntax.AutoPlaced`.** `Expr.autoPlaced full`: the flag says whether the expression starts a full expression (a declaration's type or value, a paren's inside, a tuple's or list's item, an arrow's right side), passes down the leftmost spine, and only there is the list's first item tested (`autoCall`, moved here). `autoFree1` is `autoPlaced` with the flag always on, so the new fact covers more trees. Read-back's lemmas take `autoPlaced False` below the operator level and `autoPlaced True` where `noAutoLine` needs the start (`fullHung`, `inlineHung`, `arrowHung`, `inlinePlainHung`); `autoPlacedInner` goes from one to the other.
- **`readsBackHung`** takes the type's and value's placement instead of their `within1`, and `DeclsReadBack`, `readsBackFile1` and `outputParses1` pass it up. `tidiedPlaced1` gives it for the driver's tidied tree from `Fmt.PlacedProofs.parsedPlaced1`, which is **open**: the parser's fact. Computed on 1,686 grammar1 parses, none unplaced (and none `autoFree1` but unplaced).
- **Parser side.** `Syntax.ParseKept`: `Goal.full`, `KeptAt`, and `keptPlacedUp` (placed inside, kept, and no implicit binder ahead give placed at the start). For the walk to give `KeptAt`, `Kept` itself has to carry `autoPlaced False`, since a node's inner full expressions are built inside the walk; that is the walk follow-up's.
- `autoPlacedDeaf`, `autoPlacedCalm` and `commaKeepsPlaced` (P2) are in `Fmt.PlacedProofs`.

## Slice 1 checkpoint (19 Nov 2026)

SW-4195 (Sonnet), the end-of-slice measurements of `docs/proposals/self-hosted-fmt-proof-plan.md` §4. Measured on SW-4195's worktree, which is `main` at 3ea9a5981 (after SW-4194's merge), while SW-4193 was deleting dead proofs, so the counts are a little high. The one-screen summary is `docs/reviews/SW-4195-slice1-checkpoint-numbers.md`; this section has the tables behind it. Method and scripts: counts are text counts of lines starting `theorem` in `tools/fmt/src/**/*.sw`; tests (`Tests/`) and examples are excluded (they have none). Everything is measured unless marked [estimated] or [heuristic].

### 1. Theorems per layer, against the sketch

The sketch (`docs/proposals/self-hosted-fmt-s1-sketch.md` §2) predicted by layer. Files are mapped to layers by what they prove, as the sketch describes its layers; where a file serves two, it goes to the one its statements are about [heuristic, by file name and header doc]. Counts are net new since the sketch (006bcf80f, 18 Nov 11:48): the 201 theorems that already existed then (`Fmt/Walk`, `MeaningProofs`, `BlankProofs`, `MergeProofs`, all passes) are taken off Passes.

| Layer | Files | Sketch | Actual (net new) | Times sketch's range | Times its middle |
|---|---|---|---|---|---|
| Lexer (14) | `Syntax/Lex*Proofs`, `OnceUnreturnedProofs`, `Fmt/UnreturnedProofs` | 90–130 | 348 | 2.7–3.9 | 3.2 |
| Rule N (15) | `Syntax/Settle*Proofs`, `GoodItemProofs`, `GlueQuietProofs`, `Fmt/SettleParseProofs` | 150–230 | 550 | 2.4–3.7 | 2.9 |
| Parser (16) | `Syntax/Parse*`, `Follows*`, `DeafProofs`, `AutoPlaced`; `Fmt/TraverseFail`, `PlacedProofs`, `SourcePlainProofs`, `Kinds`, `Grammar1` | 230–320 | 2,115 | 6.6–9.2 | 7.7 |
| Read-back (17) | `Syntax/ReadBack*`; `Fmt/ReadBackFile`, `SplitProofs`, `SpeltSlots`, `GroupSlots`, `PrefixHeadSplit`, `TopReadBack` | 110–160 | 667 | 4.2–6.1 | 4.9 |
| Rules and spelling (18) | the rest of `Fmt/` (hangs, lays, elements, touch, told, spell, join, stands, trivia, print) | 300–450 | 1,843 | 4.1–6.1 | 4.9 |
| Passes (19) | `Fmt/PassProofs`, `Walk`, `MergeProofs`, `BlankProofs`, `MeaningProofs`, `CalmProofs`, `CalmTopProofs` | 40–60 | 257 (458 less the 201 already there) | 4.3–6.4 | 5.1 |
| Glue (20) | `Fmt/TopStatements`, `Accepts1`, `Driver1`, `OutputStatements`, `TriviaStatements`, `Predicates`, `FinishProofs`, `OutputFileProofs`, `FileLexProofs`, `TokenProofs` | 25–40 | 251 | 6.3–10.0 | 7.7 |
| **All** | | **945–1,390** | **6,031** (6,232 in the tree) | **4.3–6.4** | **5.2** |

Gross: 6,796 `theorem` lines added and 759 removed across the non-merge commits since the sketch (a renamed or edited signature counts as one of each, so churn is overstated). The 4,900 lines SW-4154 deleted were mostly definitions and lemmas of the one-line read-back route.

Where the extra count is, against what the sketch did not plan (D3687 widened slice 1 from "quiet" declarations to the whole grammar on 19 Nov; the sketch assumed the narrower statement) [heuristic, by file group]:

| Group the sketch did not size | Theorems |
|---|---|
| Two-run parser framework (`Follows*`, `DeafProofs`, `TraverseFail`): one lemma per parser function, SW-4132's plan | 1,058 |
| The `Kept` walk (`ParseKept`, `ParseCarries*`) | 265 |
| Multi-line read-back (`ReadBackHung*`, SW-4121) | 137 |
| Comments anywhere (`Fmt/Elements*`, SW-4130) | 114 |
| Those four | 1,574 |
| The rest, against the sketch's 945–1,390 | 4,457 (3.2–4.7 times) |

So taking out everything D3687 added still leaves the count more than 2 times the sketch's top.

### 2. Lane minutes and theorems per agent hour

Method. The lane set is the board's done tickets in epic `parser-proofs` from SW-3964 on whose agent is Sonnet or Opus (a `[Sonnet]`, `[Opus]` or `[Sonnet→Opus]` title tag), about the formatter's proofs or the std they need, not paper lanes, not the slice 2 to 6a programs, not the bug fixes made in both formatters, not DeepSeek: 119 lanes. A lane's minutes are the time from the commit that records it started (`Board: … SW-N started`) to its merge commit on `main`. Check on the 38 lanes whose "Model result" line gives minutes: the median of reported over measured is 0.97 (reported total 1,164 min, measured 1,027), so the measure is good for a total; it includes the wait for a merge batch, and misses time before the board commit. 118 of the 119 lanes have both commits (SW-4139's start is in a combined commit; it counts as zero).

| | Lanes | Minutes | Hours |
|---|---|---|---|
| Opus | 66 | 2,829 | 47.2 |
| Sonnet (one Sonnet→Opus) | 52 | 1,335 | 22.2 |
| **Proof lanes** | **118** | **4,164** | **69.4** |
| Paper lanes (Fable, plus SW-4166 on Opus; sketches, statements, reviews, checkpoints) | 17 | about 703 | about 11.7 |
| Proof and paper | | about 4,867 | about 81 |

- Elapsed: 18 Nov 11:49 to 19 Nov 16:38, 28.8 hours, with up to three build lanes and paper lanes at once.
- **Theorems per agent hour:** 6,031 / 69.4 = **87 on proof lanes** (98 gross), 74 with the paper lanes counted. The toy's was 80–110; the sketch's rate was 90.
- The sketch's own lane estimate for tickets 14 to 20 was 815 minutes. The 4,164 measured is 5.1 times that; the theorem count is 5.2 times. So the rate held; the count was wrong.
- Not counted: DeepSeek lanes (not measured), the lanes for slices 2 to 6a, orchestrator and review time, Matt's time.
- Approximate: lane start is a commit time, and several paper lanes (SW-4132: 191 minutes) include a wait.

### 3. Lines per theorem

A theorem's lines run from its `theorem` line to the last line before the next line that starts in column 0 (its statement and proof; the doc comment above is not counted).

| | Slice 1 (6,232 theorems) | The toy |
|---|---|---|
| Median | 9 | 11 |
| Mean | 14.7 | 19 |
| 90th percentile | 32 | |
| Up to 5 lines | 30.7% | |

The five longest proofs:

| Lines | Theorem | File |
|---|---|---|
| 433 | `atomHung` | `Syntax/ReadBackHungAtoms.sw` |
| 346 | `edgeFacts` | `Fmt/EdgeHangProofs.sw` |
| 318 | `exprOk` | `Fmt/Walk.sw` (before slice 1: SW-3877's) |
| 316 | `elStep` | `Fmt/LaysEls.sw` |
| 303 | `declOk` | `Fmt/Walk.sw` (SW-3877's) |

### 4. What the theorems are [heuristic]

Each theorem gets the first class it fits: (a) list helper: a name containing an `Append`, `Rev`, `Map`, `Filter`, `Length`, `Take`, `Drop`, `Concat`, `Zip`, `Fold`, `Mem`, `Last`, `Head`, `Tail`, `Nth`, `Flat`, `Cons`, `Nil`, `Sum`, `Count`, `Prefix`, `Suffix`, `Cat`, `Items`, `Words`, `All…`, `Any…`, `Pair`, `Split` or `Join` piece (generous: it also catches theorems about the printer's items and words); (b) dispatcher: at most 12 lines and the proof's first step is a `cases`, `match`, `induction` or `byCases`; (c) per-function walk lemma: any other theorem in the parser walks (`Follows*`, `ParseWalk*`, `ParseCarries*`, `ParseKept`, `ReadBackRuns`, `DeafProofs`), one per parser function; (d) slice bookkeeping: at most 3 lines, or in the glue layer; (e) other.

| Class | Theorems | Share |
|---|---|---|
| Per-function walk lemmas | 1,458 | 23.4% |
| Dispatchers | 1,644 | 26.4% |
| List helpers | 732 | 11.7% |
| Slice bookkeeping | 561 | 9.0% |
| Other (the substantive statements) | 1,837 | 29.5% |

By layer, the share in no class but "other": Parser 4%, Rules and spelling 52%, Read-back 40%, Lexer 44%, Rule N 38%, Passes 37%, Glue 0%. Read as: the parser's count is almost all one lemma per parser function, which is why it is the layer furthest over (7.7 times). The dispatcher class is an upper bound: a short `cases` proof is often a real fact.

### 5. `check` time

`stitchwort check` over `tools/fmt` (the whole project), one run in this worktree, in the background at `nice -n 15`: **396 s wall (6.6 min), 388 s of user CPU**, "checked 131 namespaces of fmt". The load average was 22 at the start and 10 at the end (other lanes), but the user time shows it is CPU-bound, so the figure is near what an idle machine gives. Whether every namespace came from the check cache is not known: it is the time of the run as the cache stood in a fresh worktree (so not a cold run, and not necessarily fully warm). It prints W-UNREACHABLE warnings (about proofs, in `Syntax.FollowsDecl`).

### 6. Harness score

Not re-run: the multi-line gate (`tools/fmt/dev/multiline-gate`) copies a module into `tools/fmt/src` and rechecks the project, and a repo-wide "declarations within slice 1" count needs the corpus run over all of `aoc/`, `std` and `games/rogue`. What exists:

- SW-4119's corpus run (19 Nov 07:41, before D3687's widening): the driver accepted **380 of about 515** slice 1 definitions in the repo (74%), 355 unchanged and 25 reformatted; 114 refused only for qualified names, exponents, `auto`, `Prop`/`Type` (since widened: SW-4125, SW-4128), 29 for not printing on one line (since widened: SW-4176), 43 outside `within1`.
- SW-4185's gate at scale 0 (generated multi-line declarations; the counts are from this lane's brief, quoting SW-4185's report, not re-read): check A accepted 730 multi-line and 167 one-line cases; no FAIL; SW-4183 and SW-4176 report the same gate with no FAIL, and SW-4183 byte-identical output on 10,476 sources.
- Missing: a corpus count after the widening. It is one `stitchwort fmt` sweep with a note of which definitions refuse and why (the SW-4119 scripts are in that lane's scratch); SW-4201 is filed for it.

### 7. Top five frictions

From `docs/agent-feedback/2026-11.md` (about 100 rows for the slice 1 lanes; time costs are the lanes' own estimates, so approximate).

| # | Friction | Cost | Ticket |
|---|---|---|---|
| 1 | The checker's resource and feedback problems on large proofs: `E-RESOURCE` that names no `let` and needs hand bisection (SW-4071 15 min, SW-4077, SW-4110), checks of 2 to 5 minutes with no fast loop for one theorem, a check killed by timeout that exits 0, `rewrite` silent no-ops | about 2 to 3 hours over the slice | SW-4091, SW-4113, SW-4032 (existing); new: SW-4197 (a fast loop) |
| 2 | Proof-language behaviours the guide does not say: a `match` does not refine hypotheses or guards (SW-4006 15 min, SW-4040 10 min), `&&`, `++` associativity and `!=` as a proposition, `(..)` import name clashes, rewrite rejecting definition names (SW-4011 10 min, rediscovered), `byComputing` through hidden matches | about 2 hours | SW-3984, SW-4047, SW-4101, SW-4164 (existing); new: SW-4198 (one guide section) |
| 3 | Briefs that assume a fact, file, namespace or theorem that isn't there (about 20 rows: SW-3965 5 min, SW-4053 20 min, SW-4013 15 min, SW-4045 5 min, SW-4088 10 min) | about 2 hours | new: SW-4199 |
| 4 | The shell and scripting environment: zsh globs and word splitting, BSD `sed -i ''`, no `python3`/`jq` on PATH, polling with `sleep` blocked, a foreground check hitting the 120 s tool limit, edits to a rewrapped (formatted) file by script | about 1.5 hours | new: SW-4200 (a short "environment" section for lane briefs, and `board show --body` / `board note`) |
| 5 | The dev twin and slim-copy wrappers: stale binary answers (cache keyed on sources, SW-3962 5 min), wrapper paths in removed worktrees, `fmt:twin` run from the root, copying a test file over a source | about 40 minutes | SW-3988, SW-3976 (existing) |

### What the numbers say

Stop rules (proof plan §4): overall count over 2 times the sketch's (4.3 to 6.4 times): **fires**; two layers over 2 times (all seven are): **fires**; the projected total passing 9,000 theorems or 110 agent hours: slice 1 alone is 6,031 (67% of 9,000) and 69 to 81 hours (63 to 74% of 110), with six more slices in the plan: **fires**; rate under 40 an hour: no (87). Carry-on does not apply. The plan asks for a rethink note to Matt with options; this checkpoint gives the numbers, the note is the orchestrator's. Two readings the note should carry: the count was off but the rate held (the sketch costed a narrower slice 1, and the parser's walk is one lemma per function), and four D3687 groups are a quarter of the total.
