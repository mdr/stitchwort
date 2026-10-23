# A formatter for Stitchwort

Ticket SW-366. Status: design accepted with the decisions in §8 (23 Oct 2026).

Matt's brief: "Plan a Stitchwort formatter that we can use, including in the
VS Code extension and the Playground."

In short: `stitchwort fmt` rewrites a file's layout: indentation, spacing,
blank lines and bracket layout. It keeps every comment and every line break
the author chose, and it never changes meaning. It lives in a small new
crate that only needs the parser, so the CLI, the language server (and
through it VS Code) and the Playground's WebAssembly build all use the same
code. Before it writes anything, it re-parses its own output and checks that
the result is the same program. If that check fails, it leaves the file as it
was.

Decisions for Matt are in §8 (D1013 to D1022). §7 lists the stages.

## 1. Goals and non-goals

**Goals**

- **Never change meaning.** The output parses to the same syntax tree as
  the input (§4).
- **Never lose a comment.** Every `--` comment comes out, in the same order
  and attached to the same code.
- **Idempotent.** Formatting already-formatted code changes nothing.
  Without this, format-on-save makes edits flicker and `--check` is useless.
- **Opinionated, with no options** (D1015). gofmt showed that a formatter
  with no settings ends style arguments: "gofmt's style is no one's
  favorite, yet gofmt is everyone's favorite" (Rob Pike, Go Proverbs).
  Stitchwort has one house style, so there is nothing to configure.
- **Fast enough to run on every save**, including in the browser. It
  parses but never type-checks.
- **Works while you type.** In a file with a syntax error, it formats the
  declarations that parse and copies the broken one unchanged (§2.5).
- **Small diffs on existing code.** The first reformat of the repo should
  be reviewable (§6).

**Non-goals (for now)**

- **Re-wrapping long lines to a width.** The repo has 2,473 code lines over
  100 characters, most of them long proof terms and one-line signatures.
  Automatic wrapping would rewrite thousands of lines and needs a full
  width-aware printer for every construct. v1 keeps the author's line breaks
  (D1013, D1014). The design leaves room to add wrapping later.
- **Re-flowing comment text.** Comments are moved as whole lines; their words
  are never re-wrapped.
- **Refactoring.** It doesn't sort imports, regroup binders (`(a: Nat)
  (b: Nat)` versus `(a b: Nat)`), rename anything, or remove brackets.
- **Reformatting code inside `"""` text blocks, strings, or the `.sw`
  snippets in Markdown docs and `web/index.html`.**

## 2. Architecture

### 2.1 What we have today

- **Comments are discarded by the lexer.** `--` skips to the end of the
  line (`crates/syntax/src/lexer.rs:176-181`), and the test
  `skips_comments_but_not_arrows` pins that (`lexer.rs:942-951`). Tokens
  carry a span, a `column` and a `line_start` flag (`lexer.rs:125-133`)
  and nothing else. There is only one comment form, the `--` line comment.
  There are no block or doc comments in the language (docs/syntax.md:11).
  By convention, a doc comment is a run of `--` lines directly above a
  declaration with no blank line between (`aoc/src/Aoc/Day04/Day04.sw:29-30`).
- **The AST keeps spans but not every token.** `Expr` has no node for
  brackets: `(a)` and `a` parse the same (`crates/syntax/src/ast.rs:24-140`).
  Nested tuples become `Tuple(a, Tuple(b, c))`, and block lines become
  `Let`/`Seq`. So printing the AST from scratch, as rustfmt does, would drop
  brackets and blank lines and lose the author's choices.
- **The parser splits a file into declarations by column 0**
  (`crates/syntax/src/parser.rs:332-388`). It can also recover:
  `parse_module_recovering` keeps going after a broken declaration
  (`parser.rs:53-79`). Layout matters (`parser.rs:1-12`; docs/syntax.md:174-180):
  a line indented further continues the one above, block lines share a
  column, and arms share a column *A* deeper than the declaration.
- **There is no surface printer.** `crates/core/src/pretty.rs` prints
  *elaborated core terms* for error messages. That output has no comments,
  no sugar and no layout, so it can't be reused here.
  `crates/driver/tests/lambda_printer.rs` round-trips that printer through
  hashes. It is a useful testing pattern but not a component we can use.
- **A tree-equality check already exists.**
  `crates/syntax/src/equivalence.rs:14-41` prints a parsed module without
  its spans (`shape`), and `parse_shape` does this straight from text. Two
  files with equal shapes "mean the same to everything after the parser"
  (`equivalence.rs:13-14`). It was built for the declaration-syntax
  converter. It is the formatter's main safety check (§4).
- **Content hashes ignore layout.** `crates/core/src/hash.rs:29-31` says
  hashes leave out "binder names, local variable names … and source
  locations". So formatting must leave every declaration's hash unchanged,
  which gives a second, independent check.
- **Precedent.** The declaration-syntax converter edited text at token
  spans instead of printing the AST, because printing "would lose every
  comment and every hand-aligned column"
  (docs/proposals/declaration-syntax.md:880-898). It was checked by tree
  shape and hashes over every `.sw` file (same doc, §5.4). The formatter
  follows the same approach.

### 2.2 What established formatters do, and what we borrow

| Tool | How it works | Borrow? |
|---|---|---|
| **gofmt** (Go) | Prints from the AST. Keeps the author's line breaks and has no line width. Comments are kept in a side list and placed by position. No options. | **Yes**: no options, keep line breaks, comments placed by position. |
| **rustfmt** (Rust) | Prints from the AST and re-wraps to a width of 100. Comments are recovered from the gaps between spans, a well-known source of lost or misplaced comments. It has many options. | Its width only later. Its comment handling is a warning. |
| **Prettier** (JS/TS) and **Wadler's "prettier printer"** | Build a *document*: text, `line`, `nest`, `group`. A group is printed flat if it fits, otherwise every `line` in it breaks. Comments are attached to the nearest node before printing. | **Yes** for the document model and "a group breaks all or nothing", which is exactly D1012's bracket rule. |
| **Black** (Python) | Opinionated, and **checks after formatting that the output's AST equals the input's**, refusing to write if not. | **Yes**: the self-check in §4.1. |
| **Ormolu / Fourmolu** (Haskell, layout-sensitive like us) | Print from GHC's AST with exact text for literals, and re-parse the output to check the AST is unchanged. Ormolu keeps the author's choice between one line and several. Fourmolu adds options. | **Yes**: same AST check, and "single line versus multi line follows the input". |
| **Scalafmt** | Width-based search for the best layout. Its `newlines.source=keep` mode keeps the author's breaks. Many options. | The idea of the `keep` mode. Not its search or its options. |
| **Lean 4** | Its syntax objects carry the whitespace and comments around each token, and its pretty printer has a syntax formatter. Source formatters built on them have been attempted, but there is no standard one, largely because user-defined notation makes layout open-ended. | A warning: keep the scope small. |
| **rust-analyzer's rowan, Roslyn** | A *lossless* tree: every space and comment is "trivia" attached to a token, so the tree prints back byte for byte. | **Trivia on tokens: yes.** A full lossless tree: not now, because it means rewriting a 5,300-line parser. |

### 2.3 The design: AST for structure, tokens for text

The formatter has four steps.

1. **Lex with trivia.** A new `lex_with_trivia` returns the same tokens as
   `lex`, plus, for each token, its *trivia*: the comments before it (each
   on its own line), the number of blank lines before it, and a comment
   after it on the same line. Comments before the end of file attach to an
   end marker. The existing `lex` becomes a thin wrapper that drops the
   trivia, so the parser, the fuzz test and `skips_comments_but_not_arrows`
   don't change. This is the Roslyn/rowan trivia model without the
   lossless tree.
2. **Parse as today**, with `parse_module_recovering`, plus a way to get
   each declaration's token range and whether it parsed (§2.5).
3. **Build a layout document.** Walk the *tokens* in order, using the AST
   only to know which construct each token belongs to: header, `:=` body,
   arm, block line, bracket, `calc` step, and so on. For each token, decide:
   - **Does a new line start here?** Yes when the source had one (D1013), or
     when a D1012 bracket group breaks. A trailing comment always ends its
     line.
   - **The new line's indentation**, from the enclosing construct (§3).
     Never from the old column, except inside text blocks.
   - **Spacing between tokens on the same line**, from a small table of
     token pairs (§3). Where spacing changes meaning it is copied from the
     source: `x.f` versus `x .f`, `main()` versus `f ()`, `a - -b`, `-x`
     versus `- x`.

   The output is a Wadler/Prettier document, so later width-based
   wrapping (D1014) is a change to the document, not a rewrite.
4. **Print the document**, using each token's **original source text** from
   its span, never re-rendering it. So numbers, strings, escapes,
   qualified names and text blocks come out byte for byte.

The formatter only emits tokens and trivia it was given, in order. It never
adds or drops one, except the commas that D1012/D1017 adds or removes
(§3). So the only ways it can break meaning are layout (a line ending up at
the wrong column) and gluing two tokens together (`-` `-` into `--`). §4.1
checks for both on every run.

**Text blocks.** A `"""` literal spans several lines, and its common
indentation is removed (docs/syntax.md:794). The formatter moves the whole
literal, closing `"""` included, by the same number of columns as the line
it starts on. The string's value doesn't change, and the shape check
confirms it.

**Doc comments.** Comment lines directly above a declaration, with no blank
line between, stay attached to that declaration and move with it. A blank
line between a comment and the code after it is kept, so a section label
like `-- Characters` (`crates/elab/src/std/core/Char.sw:6`) stays separate.

### 2.4 Where the code lives

A new crate, **`crates/fmt`** (`stitchwort-fmt`), depending only on
`stitchwort-syntax`. The CLI (and the language server in it) and
`crates/web` depend on it, and none of them needs the elaborator to format.
The trivia lexer goes in `crates/syntax/src/lexer.rs` next to `lex`. The
public interface is one function:

```text
format(text) -> Ok(formatted text) | Err(diagnostics)        -- whole file
format_range(text, byte range) -> edits                      -- §5.2
```

### 2.5 Code that doesn't parse

**Decided (D1021 (b)): a file with any lexical or syntax error is refused
whole.** The formatter returns the diagnostics and changes nothing. The CLI
reports the file and exits non-zero; the editor returns no edits, silently.
Format-on-save is off by default (D1022), so refusing a half-typed file costs
little.

The option not taken, kept for reference: copy a declaration that doesn't
parse unchanged and format the rest. That works because declarations are
split by column 0 before they are parsed (`parser.rs:332-388`) and recovery
works at that granularity (`parser.rs:53-61`), so it can be added later
without redesign.

## 3. The style rules

These rules are built from D1012 and from how the repo's 877 `.sw` files
are written today (an evidence survey in this lane; the counts below are
grep-based). **Bold "D…"** marks a choice for Matt.

| # | Rule | Before | After | Evidence / note |
|---|---|---|---|---|
| R1 | Indent unit is 2 spaces. Arms at +2 from the declaration, header continuation lines at +4 | `def f (x: Nat): Nat` / `      \| Zero => 0` | `def f (x: Nat): Nat` / `  \| Zero => 0` | 6,720 lines at 2, 2,451 at 4; header continuation at 4, e.g. `crates/elab/src/std/List/Sort.sw:39-41` |
| R2 | Block lines (`let`, statements) at the block's column. A body on the next line after `:=` or `=>` is at +2 | `:=` / `    let x := 1` / `    x` | `:=` / `  let x := 1` / `  x` | `aoc/src/Aoc/Day04/Day04.sw:72-74` |
| R3 | No space before `:`, one after: `(x: Nat)`, `def f: T`, `match h: e` | `(p : x = y) : y = x` | `(p: x = y): y = x` | ~3,081 `):` against 17 `) :` (`std/core/Equality.sw:11`) |
| R4 | One space around `:=`, `=>`, `->`, `=` and binary operators; one between application arguments | `f  x  :=x+1` | `f x := x + 1` | |
| R5 | No spaces inside `(` `)` and `[` `]`; one space inside `{ }` on one line | `( a, b )`, `{a = 1}` | `(a, b)`, `{ a = 1 }` | records `{ name = "Alice", age = 30 }` |
| R6 | Comma: no space before, one after (or a line break) | `[1 ,2]` | `[1, 2]` | |
| R7 | **D1012** multi-line comma brackets: comma at the end of each line, no trailing comma, closer on its own line at the opening line's indentation (column 0 at top level) | `{ name: Text` / `, age: Nat` / `}` | `{` / `  name: Text,` / `  age: Nat` / `}` | 112 leading-comma lines today; **D1017** whether to convert them |
| R8 | A comma bracket that spans lines in the source puts one element per line. One that's on one line stays on one line | `[1, 2,` / ` 3]` | `[` / `  1,` / `  2,` / `  3` / `]` | Prettier's group; **D1017** |
| R9 | Brackets without commas (nested application arguments) keep their closers where the author put them, e.g. the `Eq.trans` staircase with `)))` | (unchanged) | (unchanged) | `Sort.sw:76-82`; **D1018** |
| R10 | Arms: `\| P => e` with exactly one space before `=>`. No column alignment | `\| None   => 0` / `\| Some x => x` | `\| None => 0` / `\| Some x => x` | ~1,387 aligned against ~3,270 not; **D1016** |
| R11 | A multi-line arm body starts on the next line at the `\|` column +2 | | | 665 arms end in `=>`; `Sort.sw:29-34` |
| R12 | `if … then … else` follows the author's breaks. A broken `else` lines up with its `if` | | | `Day04.sw:101-104` |
| R13 | Pipelines: a `\|>` that starts a line goes at +2 from the expression's first line | | | `Day04.sw:53-55` |
| R14 | `calc` steps at +2, each `_ = … := …` on its own line | | | 181 `calc`s; `Sort.sw:30-34` |
| R15 | Attributes `@[…]` stay where they are: on their own line above a declaration, or inline before a constructor or field. Spacing inside follows R4 to R6 | | | `examples/accept/attributes.sw:4,6,16` |
| R16 | Comments: an own-line comment is indented like the code line after it. A trailing comment gets exactly one space before `--`. The text after `--` is never changed | `x   -- note` | `x -- note` | trailing comments are rare (~3); **D1016** covers alignment |
| R17 | Blank lines: runs of blank lines become one. None at the start of a file or of a declaration's body. No blank line is ever *added*, so grouped tests and theorems stay grouped | three blank lines | one | 6,192 single against 17 double gaps; 1,022 declarations directly follow code; **D1020** |
| R18 | Files end with exactly one newline. No trailing spaces outside text blocks | | | `Day04.sw` has a trailing blank line |
| R19 | `namespace`, then imports with no blank line between them, then one blank line. A long import list follows R7 | | | `Day04.sw:22-23`; `std/core/Imports.sw:12-15` |
| R20 | `def main(): …` keeps `main()` written together, as the author wrote it (spacing that matters is copied, §2.3) | | | 116 written together against 1 with a space |
| R21 | A bare `:=` on its own line at column 0 after `decreasing` stays there | | | 40 such; `Day04.sw:115-117` |
| R22 | Binder grouping, the order of declarations and imports, and brackets are never changed | | | §1 non-goals |

R7 under D1012, worked through on a record type:

```text
-- before (today's leading-comma style, docs/syntax.md:262-266)
type Sized (a: Type) =
  { items: List a
  , size: Nat
  }

-- after
type Sized (a: Type) = {
  items: List a,
  size: Nat
}
```

The opening `{` moves up to the end of the `=` line. The parser must accept
this, which is what SW-365's "closer in column 0" change is for: a `}` at
column 0 must close its bracket and not start a new declaration. SW-365 has
merged (`98a1a2ab`): a column-0 `,` or closer continues an open bracket in
`split_decls`. Nested brackets put the closer at the opening line's
indentation, as D1012 says.

## 4. Correctness checks

### 4.1 Built into every run (Black's approach)

After formatting a file, before returning the result, the formatter checks:

1. **Same tokens:** lexing the output gives the same token kinds and texts,
   in the same order, with D1012 commas as the only allowed difference.
   This catches glued or split tokens.
2. **Same comments:** the same comment texts, in the same order.
3. **Same tree:** `equivalence::shape` of the output equals that of the
   input (`crates/syntax/src/equivalence.rs:16`). It ignores spans, so
   layout differences disappear and any change of meaning shows up. This
   catches every layout mistake, for example a line that was a continuation
   becoming a new block line.

If any check fails, `format` returns an internal error ("formatter bug:
output differs, file left unchanged", with the first difference). The CLI
reports it, the editor shows nothing, and nothing is written. Parsing twice
is cheap compared with type checking, so these checks stay on in release
builds.

### 4.2 Test suites (in `crates/fmt/tests`)

- **Golden tests:** a `before.sw` / `after.sw` pair per rule in §3, plus
  the D1012 cases, including nested brackets, text blocks, comments in
  every position and broken declarations.
- **Idempotence:** for every golden input and every repo file,
  `format(format(x)) == format(x)`.
- **Whole repo:** every tracked `.sw` file (877 today) formats without an
  internal error and is idempotent. `examples/reject` files that fail to lex
  must be refused, and the ones that fail to parse must have their broken
  declarations copied unchanged.
- **Hashes:** for every file that loads, load the original and the
  formatted text in fresh sessions and compare every declaration's
  `def_hash`/`data_hash`, plus the lists of tests and exports. This is
  independent of the parser-level checks, because it goes through the
  elaborator. It reuses the comparison from
  `crates/driver/tests/hash_stability.rs:39-50` and lives in
  `crates/driver/tests`, because `crates/fmt` mustn't depend on the driver.
  After the repo reformat (§6), the `hash_stability` snapshots must be
  unchanged.
- **Fuzz:** `crates/syntax/tests/fuzz.rs` already mutates examples and
  generates random token sequences. A sibling `crates/fmt/tests/fuzz.rs`
  with the same seed must show that the formatter never panics, that any
  output passes §4.1, and that it is idempotent.

## 5. Integration

### 5.1 CLI

```text
stitchwort fmt [--check] [FILES or FOLDERS...]
```

- With no arguments, it formats the project's sources (found as `check`
  does, from `stitchwort.yaml`; `crates/cli/src/main.rs:33-80`). Folders are
  searched for `.sw` files. `-` reads standard input and writes standard
  output (for editors and scripts).
- It writes files in place, and only those that changed. It prints the
  changed paths.
- `--check` writes nothing. It lists files that would change and exits 1 if
  any would, as gofmt `-l`, `rustfmt --check` and `prettier --check` do.

### 5.2 Language server and VS Code

The server advertises its capabilities in `crates/cli/src/lsp.rs:75-90` and
dispatches requests around `lsp.rs:340-410`. Add:

- `documentFormattingProvider: true` → `textDocument/formatting`. It
  formats the open document's current text and returns one edit replacing
  the whole document (or no edits if nothing changed).
- `documentRangeFormattingProvider: true` → `textDocument/rangeFormatting`.
  It formats the **whole declarations** that overlap the selection. A
  declaration is the natural unit because declarations are independent
  (§2.5).
- Errors (lexical error, internal error) return no edits, never an LSP
  error, so format-on-save never pops up a failure while you type.

The VS Code extension needs no code: `vscode-languageclient`
(`editors/vscode/package.json:12`) offers Format Document, Format Selection
and format-on-save once the server advertises these capabilities. We add
`configurationDefaults` in `package.json` setting
`"[stitchwort]": { "editor.formatOnSave": false }`. Format-on-save stays
opt-in in VS Code's own settings (D1022), and Format Document works
straight away. The README gets one paragraph.

### 5.3 Playground (static, no server)

- `crates/web/src/lib.rs` gains `#[wasm_bindgen] pub fn format(source: &str)
  -> String` returning JSON (`{"ok": true, "text": …}` or `{"ok": false,
  "diagnostics": […]}`), like the existing exports (`check`, `lib.rs:60`).
- `web/playground-worker.js` gains a `format` action in the single-file
  table and in the project table (one file at a time) (`playground-worker.js:35-51`).
- `web/index.html` gains a **Format** button next to Run, and the shortcut
  **Shift+Alt+F** (VS Code's). The new text replaces the textarea's text in
  a way the browser can undo, keeping the caret on the same token.
- Everything runs in the worker, so it fits the static-site rule.

### 5.4 CI

After the repo reformat, `stitchwort fmt --check` runs over the repo in the
test suite (a `crates/cli` test that runs the formatter library over the
file list, so `cargo test` enforces it and no extra CI step is needed),
excluding the folders in D1019.

## 6. Rollout

1. Stages F1 to F4 land (§7). The formatter exists, but nothing has been
   reformatted.
2. **A dry run:** a lane runs `fmt` over the repo on a branch and reports
   the size of the diff by folder, plus 20 sample hunks, for Matt to look
   at. Any rule that produces surprising output is fixed or taken to Matt
   before step 3.
3. **The one-off reformat:** one commit, `stitchwort fmt` over the agreed
   scope (D1019), with no other changes. The checks are: §4.1 passes for
   every file; `hash_stability` snapshots unchanged; `cargo test` passes
   (CLI snapshots that quote source lines are re-accepted only for the
   folders D1019 includes, and the diff of each re-accepted snapshot must
   be layout-only). The commit's hash goes in `.git-blame-ignore-revs` so
   `git blame` skips it.
4. From then on, the `--check` test (§5.4) keeps the repo formatted, and
   `docs/workflow.md` tells lanes to run `stitchwort fmt` before
   committing. A lane in flight when the reformat lands resolves conflicts
   in favour of its own changes, then re-runs `fmt` on the files it touched.

Timing: the reformat should land when few lanes are touching `.sw` files.

## 7. Staged plan

Each stage is one lane, with a gate it must pass before merging. Tiers:
**Opus** for design and the hard core, **Sonnet** for implementation that
needs judgement, **DeepSeek** for mechanical work.

| Stage | What | Gate | Tier |
|---|---|---|---|
| **F0** | `lex_with_trivia`: comments, blank-line counts and trailing comments on tokens. `lex` unchanged. Plus a syntax API giving each declaration's token range and whether it parsed | Unit tests. A property test over every repo `.sw`: tokens + trivia rebuild the file's text exactly, apart from spaces | Sonnet |
| **F1** | `crates/fmt` core: the document type and printer, the §4.1 self-checks, and rules for whole-declaration layout: declaration starts, R1/R2 indentation, R3 to R6 spacing, R16 to R18 comments and blank lines, text blocks, and broken declarations copied (§2.5). Constructs not handled yet are copied with only their indentation adjusted | Golden tests. Every repo file passes §4.1 and is idempotent (copying counts as passing) | **Opus** |
| **F2** | Full coverage: arms, `match`/`handle`, `if`, `calc`, `\|>`, records, data types, abilities, interfaces, attributes, imports, D1012 brackets (R7/R8), and the remaining rules | Golden test per rule. Whole repo: §4.1 + idempotence, with no constructs left on the copy path (counted, must be 0) | Sonnet |
| **F3** | Hash oracle test in `crates/driver/tests` and the formatter fuzz test | Both pass. Fuzz at the default case count runs in under 10 s in release builds | Sonnet |
| **F4** | CLI `stitchwort fmt [--check]`, including `-` for standard input | CLI tests: changed-file listing, `--check` exit codes, a broken file | DeepSeek |
| **F5** | LSP formatting and range formatting, and the VS Code `configurationDefaults` | An LSP test in the style of the existing `lsp.rs` tests: request → edits, an error → no edits. `editors/vscode/test` passes | Sonnet |
| **F6** | Playground: wasm export, worker action, Format button, Shift+Alt+F, undoable replace, caret kept | `web/test.sh` with a browser test: format, then undo restores the text | Sonnet |
| **F7** | Dry run, then the one-off repo reformat and the `--check` test (§6) | §6 step 3 checks. Matt approves the dry-run sample | DeepSeek for the run, after Matt's sign-off on the dry run |

F0 must come before F1. F2 to F3 and F4 to F6 can then run in parallel. F7
comes last. Later, if Matt wants it, a stage
**F8** (Opus) adds width-based wrapping (D1014).

**F2 as built.** Nothing is left on the copy path (`copied_lines` and
`copied_gaps` are 0 over the repo, and the repo test asserts it). Notes for
the later stages:

- Indentation is one rule: a line goes at +2 from the line it continues
  (arms, body lines, `|>`, `calc` steps and further arguments alike), and a
  definition's header lines at +4 (`decreasing` too). A parent's groups of
  children keep their order. `then`/`else` below their `if` line up with it
  (R12). A `|>` under a line of the same column goes at +2 (R13); one after a
  multi-line expression stays where it is.
- Braces: a `{` after `:` or `->` is an effect row (`result_type` in the
  parser is the only place a row can start), tight; every other brace is a
  record, spaced. Prefix and infix `-` follow the parser's position rule, and
  `<-` in `rewrite` is kept.
- Brackets are converted (D1012/D1017) unless they hold a `match`,
  `rewrite`, `handle`, `calc` or an arm at their own level (their commas may
  separate patterns) or a comma would have to share a line with two comments.
  An opener that starts a line joins the line above only if it is the only
  statement at its column, has no comment or blank line before it, and the
  line above has no trailing comment. A trailing comma is dropped, also on a
  one-line bracket. A declaration whose converted text fails the checks is
  formatted again without conversion (`Stats::unconverted_decls`, 0 over the
  repo).
- `crates/fmt/tests/golden/*.sw` are test data in the repo: F7 must leave
  them out of the reformat.

**F3 as built.** `crates/driver/tests/fmt_hashes.rs` loads every tracked
`.sw` file outside D1019's folders and `crates/fmt/tests/golden/` as written
and as formatted, in fresh sessions, and compares every declaration's
`def_hash`/`data_hash`, the export flags, the order of declarations and the
tests. Files inside a project (every `stitchwort.yaml` folder: `aoc` and the
accepted example projects) are compared by loading the whole project, with a
`Files` wrapper that formats each `.sw` it reads. Today: 217 standalone files
and 17 projects (94 files) compared, none skipped; the 55 files under
`crates/elab/src/std` are compiled into the compiler and can't be loaded
alone, so they are not covered (only the parser-level checks cover them).
`FMT_HASHES=<text>` limits a run by path. `crates/fmt/tests/fuzz.rs` uses the
syntax fuzzer's generator and seed (accepted and rejected examples, mutated,
plus token soup): no panic, no `Internal` error, and
`format(format(x)) == format(x)`; 50,000 cases take about 3 s in release
(`FUZZ_CASES` for more; 1.5 million were clean). It found one bug: a file
whose first column-0 token is `:=` made `decl_ranges` return ranges shifted
to start at token 0, so the formatter dropped or garbled tokens. Fixed in
`decl_ranges`, and the formatter keeps such leading tokens as written (golden
`leading-colon-eq*`).

## 8. Decisions for Matt

**Decided (Matt, 23 Oct 2026).** These override the recommendations and
any text above that disagrees.

| Decision | Choice |
|---|---|
| D1013 | (c): keep the author's line breaks in v1; width-based wrapping later, as F8 |
| D1014 | 120 characters: the width F8 wraps to. v1 doesn't enforce or report it |
| D1015 | (a): no options at first; add them later only if needed |
| D1016 | (a): never align |
| D1017 | (a) and (i): convert, one element per line, opener at the end of the line before. **No exception** for literal-only brackets |
| D1018 | (a): leave closers of comma-less brackets where they are |
| D1019 | (b): skip `examples/reject`, `examples/soundness`, `examples/projects/reject` |
| D1020 | (a): collapse blank-line runs to one, never add any |
| D1021 | (b): refuse a file with any syntax error (§2.5). Range formatting also needs the whole file to parse |
| D1037 | Effect rows stay tight, `{IO}`, `{Abort | e}`; records keep `{ a = 1 }` (needs the AST to tell them apart) |
| D1038 | `decreasing` lines are header continuations: +4 |
| D1039 | `f(x)` becomes `f (x)` where both parse identically; `main()`-style unit calls stay (R20) |
| D1040 | Continuation lines (e.g. further application arguments) at +2 from the line they continue |
| D1022 | VS Code's usual convention: format-on-save off by default (no `configurationDefaults` for it), Format Document works. Users opt in with `"[stitchwort]": { "editor.formatOnSave": true }` |

The original options and reasoning follow.

These are design, semantics and style choices only. Build details are
settled above.

**D1013. Line breaks: whose are they?**
- (a) Keep the author's line breaks and normalize everything else
  (gofmt, Ormolu, Scalafmt's `keep` mode).
- (b) Fully canonical: the formatter decides every break from a line width
  (Prettier, rustfmt). The same code always looks the same, but proofs
  written as staircases on purpose get reshaped, and the first reformat
  touches most of the repo.
- (c) (a) now, (b) later per construct.
- **[Recommend (a), leaving (c) open.]** It is much safer in a
  layout-sensitive language, the reformat diff stays small, and it is how
  people already lay out proofs.

**D1014. Line width.**
- (a) None, as gofmt: long lines stay long.
- (b) 100 characters, enforced by wrapping (needs D1013 (b) or (c), and
  stage F8).
- (c) 100 as a *warning* only (`fmt --check` lists lines over 100) with no
  automatic wrapping.
- **[Recommend (a) for v1.]** 2,473 code lines are over 100 today; (b) is a
  large separate project.

**D1015. Options.**
- (a) None at all.
- (b) A `fmt:` section in `stitchwort.yaml` (indent, width…).
- **[Recommend (a).]** One house style. Fourmolu exists because Ormolu said
  no, and each option doubles the test matrix.

**D1016. Alignment (`=>` in arms, trailing comments).**
- (a) Never align: one space (R10, R16).
- (b) Always align `=>` across a group of consecutive one-line arms.
- (c) Keep whatever the author did.
- **[Recommend (a).]** About 1,387 lines are aligned today, often only
  partly (`Day04.sw:39-40`). With (a) or (b), renaming one constructor
  doesn't re-pad its neighbours and blow up a diff. (c) can't be idempotent
  in a clear way. rustfmt, Prettier and Ormolu don't align; gofmt does.
  Cost: the first reformat touches those ~1,387 lines.

**D1017. Converting existing multi-line brackets to D1012.**
- (a) Convert: leading-comma layouts become trailing-comma (R7), a
  multi-line comma bracket puts one element per line (R8), and trailing
  commas are removed.
- (b) Convert leading commas only, and keep the author's grouping, e.g. a
  grid literal with several numbers per line.
- Also: where the opener goes. (i) At the end of the line before, as in
  the R7 example (`type Sized (a: Type) = {`); (ii) on a line of its own.
- **[Recommend (a) and (i), with one exception]:** a bracket whose elements are all
  number or text literals keeps its rows as written (still with D1012 commas
  and closer), so test grids and puzzle input stay readable. Prettier makes
  the same exception for number arrays.

**D1018. Closers of brackets without commas (the proof staircase).**
- (a) Leave them where the author put them, usually piled up as `)))`
  (R9).
- (b) Apply D1012's "closer on its own line" to every multi-line bracket.
- **[Recommend (a).]** D1012 was about comma lists. (b) would turn
  `Sort.sw:76-82` into a tall tower of lone `)` lines.

**D1019. What the one-off reformat and `--check` cover.**
- (a) Everything, including `examples/reject` and `examples/soundness`.
- (b) Everything except `examples/reject`, `examples/soundness` and
  `examples/projects/reject`, whose layout may be what's being tested and
  whose 566 CLI snapshots (`crates/cli/tests/snapshots`) quote source lines
  and positions.
- **[Recommend (b).]** Accepted examples, std, aoc, `web/guide` and the
  playground projects are all in scope.

**D1020. Blank lines.**
- (a) Collapse runs to one, and never add any (R17).
- (b) Also put exactly one blank line between top-level declarations.
- **[Recommend (a).]** 1,022 declarations deliberately follow code with no
  gap (grouped tests, short theorems), and (b) would split every one of
  them.

**D1021. Files with syntax errors.**
- (a) Format the declarations that parse, and copy broken ones unchanged
  (§2.5).
- (b) Refuse the whole file, as gofmt and Black do.
- **[Recommend (a).]** Format-on-save while typing needs it, and declaration
  boundaries make it safe. Lexical errors still refuse the whole file.

**D1022. Format on save in VS Code by default.**
- (a) Off: Format Document works, and format-on-save is the user's choice.
- (b) On for `.sw` files via `configurationDefaults`.
- **[Recommend (a) until the repo reformat has landed, then (b).]** Before
  the reformat, (b) would turn every small edit in an old file into a
  whole-file diff.

Not decided here, and not needed for the formatter: a separate
doc-comment syntax (such as `---`) for hover text. The formatter treats the
comment lines directly above a declaration as its doc either way, so adding
the syntax later only means a new trivia kind.
