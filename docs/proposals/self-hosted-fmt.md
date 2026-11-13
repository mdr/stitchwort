# A Stitchwort formatter written in Stitchwort

**Status:** plan, 13 November 2026 (SW-3145). Paper lane: nothing is built.
The probes were throwaway `.sw` files run with the main checkout's release
binary; they are described in [Appendix A](#appendix-a-the-probes) so they
can be rewritten. It stops for Matt's decisions ([§7](#7-questions-for-matt)).

Claims are marked **[measured]** (run for this note on Speedwell, load 3–5,
one run each, so rough), **[source]** (read in the code at `341c69c9d`) or
**[estimated]** (my reasoning, not tested).

## In plain words

**The problem.** We want a demanding, real program written in Stitchwort, to
find out where the language is slow or awkward. A formatter is a good one:
it has a lexer, a parser and a printer, a clear right answer (the Rust
formatter's output, byte for byte), and 1,695 files to test on.

**What I found.** Three things change the shape of the job.

1. *The Rust formatter does not pretty-print a syntax tree.* It works on
   the token stream, line by line: it keeps the author's line breaks, works
   out each line's indentation from how the lines' columns compare, and
   picks the spacing between neighbouring tokens from a table. The parser
   is used only as a referee: the output must parse to the same tree as the
   input, or the declaration is tried again a simpler way. So "byte
   identical" means porting this design, not writing a Wadler-style
   printer over a tree.
2. *The corpus is already formatted.* `fmt_repo` keeps every one of the
   1,695 files a fixed point, so a program that copies its input passes
   "identical on the corpus". The real test needs unformatted input: the
   51 golden pairs, the corpus with its layout disturbed, and old
   revisions of files from before each formatting rule landed.
3. *The parser is most of the code.* The lexer is about 1,300 lines of
   Rust and the formatter 1,900; the parser is 6,700. The formatter needs
   it for the referee's job and for one rewrite (dropping redundant
   parentheses), so it can come last, as its own stage.

**The change.** A new project, `tools/fmt/`, built in five stages, each
compared with the Rust formatter by one command: lexer; spacing and
indentation; the rewrites; the parser and the checks; then a speed pass
and the friction report. Every function total: no `Partial`.

**What it should do.** Format the whole tree in one process in about 20 s
[estimated, range 10–40 s]. The Rust formatter takes 7.9 s [measured], but
about 85% of that is one avoidable cost (it compares syntax trees by
printing them as text); its real work is about 1 s. So the Stitchwort
version should land at 2–5 times today's Rust formatter, and 10–30 times
what the Rust one would take with that cost removed: inside the
Python-like target. Proofs are a later stage; two useful theorems are
cheap, and a from-first-principles proof of idempotence is not.

## 1. Scope

### What the Rust formatter does [source]

`crates/fmt` (lib 201 lines, layout 1,356, spacing 200, doc 211, check 110):

1. Lex with trivia (`lex_with_trivia`): tokens with byte span, byte column
   and `line_start`; per token, the own-line comments before it, blank
   lines before it, and a trailing comment.
2. Parse the whole file; refuse it on any error (D1021).
3. Insert `∀` after theorem names (D3472), on the text, then lex again.
4. Split the tokens into declarations (`decl_ranges`: column-0 tokens).
5. Per declaration, build lines (`VLine`s), try up to four layouts
   (canonical `match` or not × brackets converted or not), and take the
   first whose text has the same tokens, comments and tree as the source;
   if none does, copy the source.
6. Check the whole output again: same tokens, comments and tree.

The layout document (`doc.rs`) is only ever given hard line breaks, so it
is a way of writing indentation, not a width-fitting printer.

### What it changes besides whitespace (the full list) [source]

| Rewrite | Where | Needs the parser? |
|---|---|---|
| Indentation of every line; spaces between tokens (R1–R6, D1037–D1040) | `indents`, `spacing::gap` | no |
| Blank-line runs to one, none at a file's or body's start; trailing spaces removed, also at the end of comments; one final newline (R17, R18) | `file`, `decl_doc`, `comment_text` | no |
| Lines of a `"""` text block move with their line (the value is the same) | `shift_lines` | no |
| Multi-line comma brackets to the D1012 layout: commas move from line starts to line ends, a trailing comma is dropped (also on one line), the closer gets its own line, the opener may join the line above | `find_convs`, `vlines` | no |
| Canonical `match` layout (D1014, D3553): `:= match x with` joins the header line if it fits in 120 bytes, else moves to its own line | `canonical_match` | no |
| `∀` inserted before a theorem's explicit parameters (D3472, SW-2657) | `insert_theorem_foralls` | no |
| Redundant parentheses dropped: after an ability row, and around a header binder's whole type (D2307, SW-2691) | `parens_to_drop` | **yes**: a pair goes only if the text without it parses to the same tree |
| Fallbacks: a declaration whose layout fails the check is retried without the canonical match, then without bracket conversion, then copied | `decl` | **yes** |
| Refusing a file with a syntax error | `format_in` | **yes** |

Everything else is kept: token text, comment text, the author's line
breaks, binder grouping, declaration order.

### In and out

**In:** all of the above, on every file of the `fmt_repo` list (1,695
files, 6.8 MB, 132,000 lines [measured]), which uses the whole surface
language. Widths and columns are counted in UTF-8 bytes, as the oracle
counts them (`∀` is 3), or the 120-column test will disagree.

**Out:** diagnostics that match the Rust ones (errors may differ, only
"refused or not" must agree); the LSP and playground hooks; range
formatting; the lexer's long explanations of invisible characters;
replacing `stitchwort fmt`.

## 2. Architecture

**Recommendation: mirror the Rust formatter's design, module for module.**
A different design (a concrete syntax tree printed with a document
algebra) would have to reproduce, by other means, behaviour that falls out
of the line-tree algorithm, such as "each deeper group of sibling lines
gets 2 more". That is more work and further from byte-identical.

- **Lexer: a state machine over `List Char`, one character a step.**
  `text.toList` once, then a function that is structurally recursive on
  the list, carrying a record (mode, the token being read, byte offset,
  byte column, a stack for `${…}` interpolation and text blocks). Lookahead
  is a pattern (`[c, d, ..rest]`). Probe 1 checked first time and needs no
  fuel or `decreasing` [measured]. Not `Std.Parse`: its combinators took
  3.7 times as long on the same job (probe 3) [measured], and the lexer's
  shape is a state machine anyway. Not `Text.get`: it is O(n) through
  `toList` [source]. Identifiers are ASCII; Unicode appears only as a
  fixed table of aliases (`∀`, `→`, `≤`, …) and inside strings and
  comments [source], so no Unicode tables are needed. Each token keeps its
  own source `Text`, since there is no way to slice a `Text` cheaply.
- **Tokens and lines in `Array`s; passes by index.** The Rust layout code
  indexes tokens and lines freely (`tokens[k - 1]`, `parent[i]`). `Array`
  gives O(1) `get` and in-place `set` when unshared [source]. A pass is
  `def pass (k: Nat) …  decreasing tokens.size - k`, which the checker
  proves by itself (probe 2) [measured]. Stacks are lists; the per-declaration
  hash maps become `Map`s keyed by small records or pairs.
- **Parser: hand-written recursive descent over the token array, with
  fuel.** The grammar is layout-sensitive (columns decide where blocks
  end), so it is a port of the Rust parser, not a combinator grammar. Its
  recursion is not structural, and proving every sub-parser consumes input
  would be a large proof effort for no user benefit, so each call takes
  `fuel: Nat`, started at the token count plus a margin, as `Std.Parse`
  does (`manyFrom`, `recursiveFuel`) [source]. Running out is reported as
  a refusal. The tree carries **no spans**, so "same tree" is derived
  equality, not the Rust version's compare-the-debug-text.
- **Printer: lines straight to a list of `Text`s, joined once.** No
  document algebra: with only hard breaks it adds nothing. Output is built
  newest-first and reversed, never by repeated `++` on a growing text.
- **Errors:** `Result` with a small error type (`Refused`, `Internal`).
  Whether to carry them with the `Fail` ability or by hand is a
  measurement for stage 1 (handler cost per token is unknown).
- **Running it:** `IO` has standard input, standard output and arguments,
  and no file access [source]. So the program is a filter: one file on
  stdin, or with `--batch` a stream of files, each after a header line
  giving its path and length, answered in the same framing. A 20-line
  shell or Rust driver feeds it the file list. This keeps the whole tree
  to one process.

### Totality

| Part | How it terminates |
|---|---|
| Lexer | structural on the character list |
| Declaration split, roles, bracket finding, line building, spacing | index passes with `decreasing size - k`; inner "pop while" loops are structural on the stack list |
| Indentation (`indents`) | the same; the sibling-group pass folds over a sorted list |
| Paren dropping (`loop { find a pair; drop it }`) | fuel: the number of parentheses |
| Parser | fuel: tokens left plus a margin |
| Printer | structural on the lines |

`main` is `{IO}` only. No `Partial` anywhere is a stage checkpoint.

## 3. Performance

**Baseline [measured].** `stitchwort fmt --check` over the 1,695 files in
one process: 7.9 s. A sample of that run puts about 85% of its time in
`equivalence::shape`, which pretty-prints each tree with `{:#?}` to
compare them (twice per file, and twice more for each declaration whose
text changes). Lexing, parsing
and layout together are about 1 s. On the three largest std files (473 KB)
it takes 0.85 s.

**Probes [measured]** (`run --native`; times after subtracting 0.45 s of
checking and compiling the probe):

| Probe | 1 MB of corpus | whole corpus as one 6.8 MB input |
|---|---|---|
| 1: state-machine scanner (words, numbers, symbols, comments, columns) and reprint | 0.27 s, 420 MB peak | 3.8 s, 2.2 GB peak |
| 2: the scanner, tokens to an `Array`, one neighbour-reading index pass with an in-place table, one `Map` fold | 0.26 s | 6.1 s, 0.9 GB |
| 3: the same tokens counted with `Std.Parse` (`many`, `oneOf`, `takeWhile`) | 0.97 s | not run |

So a simple lexer costs about 0.25 µs a character, about 1.2 µs a token;
on the 473 KB of large files, 0.15 s against the Rust formatter's 0.85 s.

**Estimate.** The formatter lexes and parses each file two to four times
(source and output; again per declaration that changes), and
runs a dozen passes over tokens and lines. At 0.3 s/MB for the full lexer,
0.2–0.5 s/MB a parse, and 0.5 s/MB for layout and printing, that is 2–4 s
per MB, so **15–30 s for the tree; I'd plan on 20 s** [estimated]. That is
2–5× the Rust formatter as it is, and 10–30× the Rust formatter if its
tree comparison were made cheap (worth a ticket of its own: about 5× on
`stitchwort fmt` for a small change [estimated]; speed work is paused, so
backlog).

**Proposed target:** the whole tree in one process in under 30 s on
Speedwell, peak memory under 1 GB, and no file more than 30× its Rust
time.

**Expected limits, most likely first.**

1. *Allocation per character.* A `List Char` is a heap cell per character,
   and the per-character state record is rebuilt each step unless the
   runtime reuses it in place. 2.2 GB for a 6.8 MB input [measured] is
   about 300 bytes a character across the copies. Per file this is fine
   (the largest is 186 KB), but it is the first thing a profile will show.
2. *No cheap text slices or builder.* `Text` at run time is one string
   [source], but there is no O(1) `slice`, no indexed read, and no
   builder, so tokens are built by reversing character lists.
3. *The parser's small allocations:* a `Result` or pair per call, fuel
   threading, and closures.
4. *Accidental array sharing:* a `set` on a shared array copies it, which
   turns a pass quadratic. The runtime counts such copies, which will find
   them.
5. *Large heaps slow down more than linearly:* probe 2 took 23× as long on
   6.8× the input [measured]. One file at a time avoids it; it is worth a
   ticket.
6. *Start-up:* `run --native` spends 0.45 s checking and compiling each
   time [measured]; the harness needs a `build --native` executable. (In
   the main checkout today that executable fails to start, "tables written
   by a different build of the runtime": the runtime library in
   `target/release` is a day older than the CLI. `task build` should cure
   it; not investigated.)
7. *Unknown:* ability handlers per token, `Map` with compound keys,
   derived equality on a 100-constructor token type, and how long the
   checker takes on a 5,000-line project with a large mutually recursive
   parser.

**To measure at each stage:** seconds per MB on a fixed 1 MB sample and on
the three largest files; peak memory; the array-copy count; a profile
(`run --profile`, `task profile:native`) of the slowest file. Each stage's
report gives these numbers, so regressions show.

## 4. Testing

- **The oracle harness** (`task fmt:oracle`): builds the native
  executable, feeds it inputs in batch mode, and compares each output
  byte for byte with the Rust formatter's, printing the counts and the
  first differing file and line. The Rust outputs are written once to a
  cache folder outside the repo, keyed by the input's and the `crates/fmt`
  sources' hashes, so a rerun costs only the Stitchwort side (about 20 s
  for everything [estimated]). Refusals are compared as "refused or not".
- **Inputs**, none committed beyond what is there:
  1. the 51 golden `before` files (`crates/fmt/tests/it/golden`), which
     cover each rule: the lane-sized test;
  2. the 1,695 corpus files as they are (tests the fixed point);
  3. the corpus disturbed, generated at run time from a seed by a small
     Rust tool that uses the real lexer's spans: indentation scaled ×2 and
     ×3 (keeps the column order, so the program is the same), spaces
     between tokens squeezed and doubled, blank lines and trailing spaces
     added, trailing commas moved to leading;
  4. old revisions from git: each file just before the commits that
     reformatted the repo (the first reformat, the `∀` sweep, the
     canonical `match` change), which is real unformatted code.
- **A token dump** from the Rust side (kind, span, column, `line_start`,
  trivia; one line a token), behind a dev-only command, so stage 1 is
  compared exactly and not just by round trip.
- **Itself:** the project's own `.sw` files join the `fmt_repo` list, and
  the formatter formatting its own source is a named test.
- **Lanes and the budget:** a lane runs the goldens and a handful of named
  files (seconds). The full oracle run is a broader suite: the verifier
  runs it after a merge that touches `tools/fmt` or `crates/fmt`, and
  Overmind in its rolling check.

## 5. Proofs (a later stage)

**Cheap and worth having: theorems about the checks, not the layout.**
Because the formatter returns a result only after checking it, some
properties hold by construction, and their proofs unfold the definition of
`format` and never mention indentation rules. (Sketches: the names are
not settled.)

```stitchwort
-- Only layout changes, up to the listed rewrites: the output's tokens are
-- the input's, once commas, parentheses and the theorem ∀s are set aside,
-- and its comments are the same in the same order.
theorem formatKeepsTokens ∀ (source output: Text) (h: format source = Ok output):
    (lex output).map Lexed.essentialTokens = (lex source).map Lexed.essentialTokens
      ∧ (lex output).map Lexed.comments = (lex source).map Lexed.comments

-- The meaning is unchanged, as far as the parser can see.
theorem formatKeepsTree ∀ (source output: Text) (h: format source = Ok output):
    parse output = parse source
```

About a day each [estimated], Sonnet. They are honest about what "only
whitespace changes" means: the exceptions (commas, parentheses, `∀`, text
block indentation) are in the statement.

**Idempotence, two ways.**

- *By validation (cheap):* define `formatStable source` as `format
  source`, kept only if formatting the result again gives the same text.
  Then `formatStable source = Ok output → formatStable output = Ok
  output` is a few lines. It doubles the run time, and it proves the
  wrapper, not the rules. A day [estimated].
- *From the rules (not recommended now):* a real proof that `format
  (format x) = format x` needs "the lexer reads printed tokens back as
  the same tokens", "new indentation preserves the order of columns, so
  the line tree is the same", and the same for brackets and `match`. The
  Rust formatter's own idempotence is known only from fuzzing, which
  found bugs as late as 10 November (SW-2466). Weeks to months of Opus
  time, and each oracle change would break it [estimated].

**Middle ground: properties of parts** (each 2–5 days, Opus) [estimated]:

- the lexer round trip, `(lexWithGaps source).render = source`;
- the output is tidy: no line ends in a space, no two blank lines in a
  row, exactly one final newline;
- `shiftLines` keeps a text block's value;
- the core indentation lemma: the line tree depends only on how columns
  compare, and the new indentation keeps those comparisons.

## 6. Stages

Times are lane hours [estimated]; each stage ends with its oracle count,
its speed numbers and friction notes in `tools/fmt/NOTES.md`.

| Stage | What | Checkpoint against the oracle | Model | Hours |
|---|---|---|---|---|
| 0 | Harness: batch driver, disturbed-corpus generator, token dump, cached Rust outputs. Count, over all inputs, how often the Rust formatter takes a fallback and how many parenthesis candidates there are | the harness reports 0 of N identical for a copy-the-input stub on disturbed input | Sonnet | 2–3 |
| 1 | Project skeleton, lexer with trivia, batch `main` | token dump identical on all 1,695 files and the goldens; `render (lex x) = x` | Opus (sets the project's shape; first friction notes) | 3–4 |
| 2 | Declaration split, token roles, spacing table, lines, indentation, comments and blank lines, text blocks | identical on the corpus as it is, and on disturbed spacing and indentation | Opus | 4–6 |
| 3 | Bracket conversion, canonical `match`, `∀` insertion | identical on the goldens and all disturbed and historical inputs, except those stage 0 counted as needing the parser | Sonnet (rules with a clear oracle) | 4–6 |
| 4 | Parser to a span-free tree (in two or three lanes: expressions and patterns; declarations and sections; types and proofs), the three checks, fallbacks, paren dropping, refusal | identical on everything; refuses exactly the files the oracle refuses in `examples/reject` | Opus for the first lane, Sonnet after | 10–16 |
| 5 | Speed pass from profiles; the friction report; tickets for each gap | under 30 s for the tree | Sonnet, Opus for the report | 3–4 |
| 6 | Proofs (optional): the three cheap theorems, then parts if wanted | `task audit:touched` clean | Sonnet, Opus for parts | 3 days, then open |

Stages 0–5: 26–39 lane hours. Stage 3 can start beside stage 2's second
half; stage 4's lanes can run in parallel after the first.

**Risks.**

- *The parser is big.* It may take longer than everything else together.
  It is last so that stages 1–3 pay off without it, and stage 0 says how
  much it buys.
- *The oracle moves.* `layout.rs` changed today (SW-2691), and SW-3142
  will touch it again. Every change to `crates/fmt` or the parser needs
  the twin updated (Q4).
- *Byte-identical is all or nothing on details:* byte columns, `\r`
  handling, the 120-byte test. The goldens and the disturbed corpus are
  there to find these early.
- *Checker time on a large project* could make the edit loop slow; this
  is a finding, not a blocker.

**Gaps I expect it to expose** (each becomes a ticket when hit):

- no file access in `IO` (read, write, list a folder);
- no `Text` slice, indexed read or builder;
- no hash map; `Map` needs an order on compound keys;
- early exit: the Rust code leans on `let … else { return }` and `?`;
  Stitchwort's equivalents are nested matches or an ability;
- loops with several changing variables become recursive helpers with long
  parameter lists or state records;
- deriving equality and printing for a token type with about 100
  constructors, and a tree type with dozens;
- termination checking of a large group of mutually recursive functions;
- memory per character, and the slowdown on large heaps;
- `build --native` and the runtime library drifting apart in a checkout.

## 7. Questions for Matt

1. **Mirror the Rust design, not a tree pretty-printer?** The oracle is a
   token-and-line formatter with the parser as referee; byte-identical
   output means porting that. The program still has a full lexer, parser
   and printer. *Recommendation: yes, mirror it.*
2. **Is the parser in scope?** Without it (stages 0–3) the formatter is
   identical wherever the Rust one's first attempt passes its check and no
   parentheses are candidates for dropping (stage 0 measures how often),
   never refuses a broken file, and has no safety check. With it, the
   project roughly doubles. *Recommendation: yes, as stage 4: it is the
   most demanding part, which is the point, and a Stitchwort parser of
   Stitchwort is reusable.* Decide after stage 0's counts if you prefer.
3. **Files: a batch stream now, or file access in `IO` first?** File
   access is a user-visible language feature needing its own design.
   *Recommendation: batch stream now; file a design ticket for file
   access, raised in priority by this project.*
4. **Once identical, must it stay identical?** *Recommendation: no merge
   gate. The oracle run reports drift; the twin is caught up in batches,
   and may lag a rule change by a day or two.*
5. **The speed target:** under 30 s for the tree in one process (about 4×
   today's Rust formatter, about 25× its real work). *Recommendation:
   accept, and revisit after stage 2's numbers.*

## Appendix A: the probes

All in the lane's scratchpad, run with `stitchwort run --native FILE <
INPUT`; the corpus is the 1,695 `fmt_repo` files concatenated (6.8 MB),
and the 1 MB input its first million bytes.

- **Probe 1** (55 lines): `type Scan = { mode, current, column,
  startColumn, fresh, tokens }`; `Scan.step (s) (c) (next: Option Char)`
  moves between `Between`, `InWord`, `InNumber` and `InComment`; `scan`
  is structural on `List Char`; tokens keep their characters, column and
  whether they start a line; `render` prints them back with one space or
  a newline between. Counts 211,883 tokens in 1 MB.
- **Probe 2:** probe 1's tokens `.toArray`, then `roles (tokens) (k)
  (found) (columns: Array Nat)` with `decreasing tokens.size - k`, reading
  `k - 1` and `k + 1` and doing `columns.modify` in place; then a
  `Map Nat Nat` fold over the tokens.
- **Probe 3:** `Parse.all input (() => many token)` where `token` is
  `oneOf [takeWhile1 isWordChar, satisfy (not blank)]` then
  `takeWhile isBlank`.
- **The Rust profile:** `/usr/bin/sample` for 4 s on `stitchwort fmt
  --check` over the file list; 2,246 of about 2,650 main-thread samples
  were in `core::fmt` writing under `equivalence::shape`.
