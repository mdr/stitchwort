# Recovering from syntax errors while someone types

**Status:** design note, 7 November 2026 (SW-1917). Waiting for Matt's
decisions D2780–D2785. Builds on the two syntax reviews
(`docs/reviews/code-review-syntax-opus.md` F2, F8, F11, F12;
`docs/reviews/code-review-syntax.md` F1, F8) without repeating them. It
covers SW-1873 (D2670, D2690) and SW-1917 (D2692). Read only: nothing was
built or run, and every claim below comes from reading the code at
`e35f954ad`.

## What this buys

While you type, the file almost never parses: a theorem is half written, a
`"` hasn't met its partner yet, an arm ends in `=>`. What the editor shows
at those moments is what the editor shows most. Today:

- **One stray character blanks the whole file**, and other files with it.
  Type an opening `"` in a 600-line file and, until you type the closing
  one, the file has no declarations: no outline, no hovers, no errors for
  the other 599 lines. Every file that imports it reports its namespace
  as missing.
- **A half-typed theorem loses everything inside it.** Type
  `rewrite Nat.addZero n in` and stop to think: the theorem disappears, so
  there's no goal to look at, which is the moment you want one, and every
  use of the theorem elsewhere is "failed".

After this note's stages:

- A lexical error costs only the declaration it's in. The rest of the file
  keeps its outline, hovers and errors, and the project still knows the
  file's namespace.
- A declaration whose body breaks keeps its signature, so its uses elsewhere
  still check against its type.
- The point where the text runs out becomes a hole. The editor shows the
  goal there, with the `let`s and parameters in scope, exactly as if you had
  typed `?`. The half-typed `rewrite … in` shows the rewritten goal.

None of this changes what a correct file means, and a file with a syntax
error still never checks as passed, never enters the check cache, and is
never formatted.

## 1. How it works today

### 1.1 Lexing

`lex_keeping` (lexer.rs:297) returns at its first error. There are about a
dozen places: a newline inside `"…${` (lexer.rs:334), a tab (:355),
character literals (:527, :554), a non-ASCII character that isn't an alias,
such as `∀`, the `é` of `café` or a byte-order mark (:578), a lone `@` or
other stray ASCII (:717, :727), a string open at the end of the file
(:749), the `"""` pre-scan (`scan_block`, :797 onwards), one-line strings
(`scan_string`, :963) and escapes (`escape`, :986).

`parse_module_recovering` then gives up: `Module::default()` and one
diagnostic (parser.rs:88–93). An indented first token does the same
(parser.rs:98–101, from `split_decls`, :406–414).

The empty module then cascades:

- the driver doesn't elaborate an empty module with errors
  (driver.rs:674–677);
- the project falls back to `parse_namespace_line` (project.rs:792,
  live.rs:892), which lexes the whole text again (parser.rs:283) and fails
  in the same place, so the file is dropped (`continue`) and its importers
  report the namespace missing.

### 1.2 Parsing

Recovery is per declaration. `split_decls` cuts the tokens at column 0
(parser.rs:406–490). Each group gets a fresh `Parser`. If it fails, the
whole declaration is left out and the names it would have declared go in
`Module::failed` (parser.rs:175–183, `declared_names_of` at :196). The
elaborator declares those names as failed, so their uses are quietly
`E-FAILED-DEPENDENCY` rather than unknown (elab module.rs:1093–1112).

Inside a declaration there's no recovery at all. Every parse function
returns `Result`, and the first `Err` unwinds to the group loop. Two facts
make finer recovery easier than it looks:

- **The parser never backtracks.** No code resets `self.pos`, and no caller
  turns an `Err` into another try. The only `.ok()` on a parse result is
  the namespace name in an error message (parser.rs:144). Every choice is
  made by looking ahead at tokens. So turning some errors into "succeeded,
  with an error recorded" can't change how any correct text parses: no
  correct parse ever went through an `Err`. (Confidence high: I grepped for
  `self.pos =`, `.ok()`, `.is_ok()`, `if let Ok` and `Err(_) =>` in
  `parser.rs` and `parser/`.)
- **The statement and arm boundaries are already explicit.** `block`
  (parser.rs:2162) runs one `statement` per line at the block's column;
  `arms` (declarations.rs:593) runs one `arm` per `|` at the arms' column.
  These are the natural places to catch an error and carry on.

What makes it risky is the eight mode fields (`limit`, `allow`,
`calc_depth`, `rewrite_rule`, `guard_start`, `rewrite_at`, `let_value`,
`in_list`; parser.rs:507–545). Each site saves and restores the ones it
changes by hand, and some don't restore on the error path. That's harmless
today only because an error throws the parser away (Opus review F8).

### 1.3 After parsing

- **Holes already exist.** `?` is `Expr::Goal` (ast.rs:95–98). The
  elaborator makes it a frozen metavariable that nothing can solve, records
  the goal (its type and the names in scope) and carries on (elab
  goals.rs:1–18). A term with one in it can't be zonked, so it **never
  reaches the kernel**, and what uses it is "unfinished" too. The machinery
  a recovered hole needs is already there and already trusted.
- **The check cache already refuses files with syntax errors.** A
  namespace with parse errors gets no cache key ("a namespace with syntax
  errors is checked without its broken declarations, so its result is never
  cached", project.rs:606–610), isn't "certain" when the plan is made
  (project.rs:247), and its outcome is `Failed` because the parse errors are
  merged into its errors (project.rs:338–345). Its importers are skipped
  with one `E-NAMESPACE-FAILED` (project.rs:296–303). Test results are
  cached by the content hash of the test's own elaborated term
  (driver.rs:1317), so they are true of that term whatever the file
  around it.
- **The formatter refuses a file that doesn't parse**: it lexes and parses
  strictly (fmt lib.rs:92–94).
- **A header with no body is a primitive** "for the elaborator to admit or
  refuse" (declarations.rs:375). So "keep the signature" must never mean
  "drop the body": that would turn a half-typed `def` into a primitive.

## 2. Designs compared

### Design A: a lossless syntax tree (rust-analyzer, Roslyn)

Rewrite the parser to build a concrete tree that keeps every token,
including the ones it couldn't use, with error nodes for the bad parts. The
typed tree the elaborator reads becomes a view over it.

- **Gains:** the parser can never fail; the formatter could format a file
  with errors (it would see every token); incremental reparsing for the
  editor; one tree for the formatter and the parser.
- **Costs:** a rewrite of an 8,876-line parser and of every consumer of
  `ast.rs`: the elaborator, formatter, navigation, docs. Weeks of lanes,
  most of them on Opus, with every syntax lane blocked meanwhile.

### Design B: targeted recovery in the parser we have (recommended)

Keep the recursive-descent parser and the typed tree. Add:

1. an **error token** from the lexer, which carries on after it;
2. a **missing-expression node**, `Expr::Missing`, that the elaborator
   treats as a hole;
3. **four recovery points**: where an expression is wanted and the line has
   ended; a block's line; an arm; a definition's body.

- **Gains:** everything in "What this buys", in about five lanes.
- **Costs:** a new `Expr` variant, which every exhaustive match on `Expr`
  must handle (about 13 places outside the parser that match `Expr::Goal`
  today, which the compiler will list); an `errors` list on the parser;
  care with the mode fields at each recovery point.
- **Rules out:** formatting a file with errors, for now (D2783). Nothing in
  it gets in the way of Design A later: the recovery points and the corpus
  tests carry over.

### Design C: resynchronise only

On any error, lexical or syntactic, skip to the next column-0 declaration
keyword and drop the declaration whole. This is the minimum for SW-1873,
and stage 2 below does it for lexical errors that leave nothing better. But
it doesn't touch SW-1917: the half-typed theorem still loses its goals and
its signature.

**Recommendation: B.** It gives the editor everything the brief asks for at
a small fraction of A's cost, and it reuses the goal machinery that already
keeps unfinished work away from the kernel.

## 3. Lexical recovery (SW-1873)

### The problem

You type `"` to start a string in the middle of a file. Until you type the
closing one, the file has no declarations, and the files that import it say
its namespace doesn't exist.

### The change

`lex_keeping` stops returning at errors. It records each diagnostic,
recovers in one of three ways, and carries on. The strict entry points
(`lex`, `lex_with_trivia`, `lex_with_bars`) keep their signatures and
return the first error when there is one, so the formatter and
`parse_expression` behave as now. A new `lex_recovering` returns the tokens
and every error, and `parse_module_recovering` and `parse_namespace_line`
use it.

| Error | Recovery |
|---|---|
| A tab; a byte-order mark not at the start; a no-break or zero-width space | Report it, then read it as a space. The tokens around it are the right ones, and the column is off by at most the tab's width, which is an error anyway. (A BOM at offset 0 is D2691's question, separate.) |
| A character that starts nothing (`∀`, `$`, a lone `@`, `#`) | A `Tok::Error` token over that character. A run of letters with a non-ASCII one among them (`café`) is one `Tok::Error` over the whole word, so the message names the word. |
| An unclosed `"` or `'`, a newline inside `"…${`, a bad character literal | A `Tok::Error` from the quote to the end of the line. These literals can't span lines, so the next line lexes as it would anyway. |
| An unknown escape (`\q`) | Report it and keep the string, without that character. |
| An unclosed `"""` | A `Tok::Error` from the `"""` to the end of the line before the next line that starts in column 0 with a declaration keyword, or to the end of the file. (D2784.) |
| Any other error inside a `"""` text (an escape, a `${…}` the two scanners disagree on, SW-1916) | One `Tok::Error` over the whole text, up to its closing `"""` (found by a plain scan for the next `"""`), or by the rule above if there isn't one. |

The `"""` rows don't depend on the `${…}` pre-scan (F1, SW-1916). Recovery
only needs to find where the text ends, which is a plain search forward.
Whatever it finds, the file already has an error, so a different choice
only changes how much is lost, never what a correct file means. That's
the rule for every recovery position in this note: **it only moves
forward, and any choice is safe, because the error is already reported**.

Downstream of the lexer:

- **The parser treats `Tok::Error` as an unexpected token** and recovers
  as in §4. An error at a `Tok::Error` adds no diagnostic of its own: the
  lexer's message is the one that says what's wrong.
- **`split_decls` stops failing.** Tokens before the first column-0 token
  (F12), and a file whose first column-0 token is `:=` (F11), become a
  group that fails with "declarations start at the beginning of a line",
  and the rest of the file parses.
- **The namespace comes from the parse.** With lexing recovered,
  `parse_module_recovering` returns the namespace line whenever that line
  itself is intact. The fallbacks in project.rs:792 and live.rs:892 then
  use `module.namespace`. `parse_namespace_line` uses `lex_recovering`
  and reads only the first group.
- **The driver's "empty module" shortcut** (driver.rs:674–677) stays, but
  now applies only to a file with nothing in it that parsed.

### What it should do, and how we'd know

- A file with an unclosed `"` in its third declaration has that declaration
  failed (its names in `Module::failed`), and every other declaration,
  the namespace and the imports as in the file without it.
- `parse_module_within` and `lex` return exactly what they return today on
  every file in the repository: correct files are unchanged, and a file
  with an error still fails strictly.
- In a project, the file keeps its namespace, and its importers get one
  `E-NAMESPACE-FAILED` ("has errors"), not "unknown namespace".

## 4. Recovery inside a declaration (SW-1917)

### The problem

```
theorem addZeroTwice (n: Nat): n + 0 + 0 = n :=
  rewrite Nat.addZero n in
```

You've typed the `rewrite` and want to see what's left to prove. Today the
whole theorem is dropped: no goal, no hover on `n`, and every use of
`addZeroTwice` elsewhere in the namespace is a failed dependency.

### The change: a missing-expression node

Add `Expr::Missing(Span)` to `ast.rs`: "the source has a syntax error here;
the parser found no expression". The elaborator checks it exactly as it
checks `?`: a frozen metavariable, with the goal recorded. Three things are
different from `?`:

- **Its declaration fails; it isn't "unfinished".** The syntax error is
  already reported, so the elaborator adds no diagnostic of its own for
  the hole, and the declaration's status is "has errors" (module.rs:625–640
  is where a declaration with only `?`s becomes `Severity::Goal`; there, a
  `Missing` makes it an error).
- **Its goal goes to the editor, not the terminal.** The editor shows it in
  the goal view and on hover at the hole. `stitchwort check` prints only
  the syntax error, since a goal for text you haven't written is noise
  there. (An implementation choice I've made; say if you'd rather see them.)
- **No code actions on it.** The "fill this goal" actions on `?` edit the
  `?`'s text, and a `Missing` has none.

Why a new node and not `Expr::Goal` again: the three differences above
would otherwise need a side table of "which goals were made up", which every
consumer must remember to consult. A variant is checked by the compiler, and
rust-analyzer's `hir` uses the same thing (its `Expr::Missing`).

**Where `Missing` may appear:** only in a `def`, `theorem`, `instance` or
`test`: in their signatures and bodies, and in local definitions. In a
`type`, `interface`, `ability`, `namespace` or `import`, the parser doesn't
recover, and the declaration fails whole as today. A data type with a
missing field type, or a constructor dropped, would change what every match
on it means. I haven't checked that the elaborator keeps a data type with a
frozen metavariable in it away from the kernel, and there's little to gain
in trying (confidence in that gap: high; in the risk: medium).

### The change: four recovery points

Each one catches an error from inside it, records it, puts a `Missing` where
the broken text was, moves forward to a point it can carry on from, and
returns success. The innermost one that applies wins, so a broken line deep
in a nested block costs only the rest of that block.

1. **The expression ran out** (`atom_base`'s last arm, parser.rs:4902).
   When an expression is wanted and `peek()` is `None`, because the line,
   the block, the arm or the declaration has ended, the parser records
   "expected an expression" and returns `Missing` at the point just after
   the last token. It consumes nothing, so the parser carries on exactly as
   if an expression had been there. This one point covers most of what
   people type: `:=` with nothing after it, a trailing operator (`a ++`),
   `=>` at the end of an arm, `rewrite h in` at the end of a line, `let x :=`
   with the value still to come, a `calc` step's missing justification.
   When the next token is something else (a `)`, a keyword, a
   `Tok::Error`), it stays an error, and the next point up catches it.
2. **A line of a block** (`block`, parser.rs:2162). If a statement fails,
   the block keeps the lines before it, and its result becomes `Missing`
   over the failed line and every line after it at the block's column,
   skipped until the first line that starts left of the block's column.
   The block then reads `let a := …; let b := …; ?`. That's the goal you
   want while typing the next line of a proof: everything above it is in
   scope.
3. **An arm** (`arm`, declarations.rs:668, and a `match`'s alternatives,
   parser.rs:2602 onwards). If the patterns parsed and the body failed, the
   arm keeps its patterns and gets `Missing` as its body. The parser skips
   to the next `|` at the arms' column, or to the end of the arms. If the
   patterns themselves failed, the arm can't be kept (dropping it, or
   reading it as `_`, would change which cases are covered, and so the
   errors about the other arms), and the error goes up to point 4.
4. **A definition's body** (`definition`, declarations.rs:313–360, and
   `finish`, parser.rs:1177). If the `:=` body, the arms, or the check that
   nothing follows the declaration fails, the declaration keeps its
   `Decl::Signature` and gets one equation with the header's patterns and
   `Missing` as its body (never no body: §1.3, primitives). The parser skips
   to the end of the group.

If the header itself fails (the name, parameters or type, past what point 1
covers), the declaration is dropped and its names go in `Module::failed`,
as today.

**Limits are never recovered.** An `E-RESOURCE` from `deeper()`
(parser.rs:716) goes past every recovery point and fails the declaration as
now (D2543: a limit fails; it doesn't give a different answer).

**The mode fields.** At each recovery point, the parser takes a copy of all
eight mode fields before trying, and puts the copy back on an error before
it carries on. The state after recovery is the state on entry, whatever the
failed path did. That's enough for recovery, and much smaller than F8's
proposal of putting every save and restore behind a guard: the fields are
read only on the paths that go on parsing, and those paths now start from a
known state. (They become one `Copy` struct, `Modes`, so the copy is one
line, and a field added later is in it automatically.)

**Errors per declaration.** `Parser` gets an `errors: Vec<Diagnostic>`. A
declaration that recovered is `Ok` with errors, and the group loop
(parser.rs:102–188) moves them to the module's errors. The strict entry
points (`parse_module_within`, `parse_expression`, `namespace_line`) fail
when the list isn't empty. That gives an invariant to test: **the error
list is empty exactly when the tree has no `Missing`.**

### Error positions

- A lexical error points at the bad character, or at the opening quote and
  the rest of its line.
- "expected an expression" at point 1 points at the place just after the
  last token, which is usually where the cursor is, with a second label on
  the token that ended the line when there is one. Today the error points
  at that token, often on a later line, or in the next declaration.
- `Missing`'s own span is the same point, or, at points 2 to 4, the tokens
  it stands for, so a hover anywhere over the broken text shows the goal.
- At most one diagnostic per recovery point: what's skipped isn't parsed,
  so it can't produce more.

### What it should do, and how we'd know

- The example above shows one goal, `n + 0 = n` (the statement after the
  rewrite), with `n` in scope, and uses of `addZeroTwice` elsewhere check against its
  type.
- A 200-line `def` with a broken line keeps its signature, and the
  lines above the broken one keep their hovers.
- The declaration with the error is never sent to the kernel. A
  `Missing` makes it impossible: the zonk fails (goals.rs:14–18).

## 5. Downstream effects

| Consumer | What it does with a recovered declaration |
|---|---|
| Elaborator | Checks it with `Missing` as a hole. It never reaches the kernel, and what uses it is unfinished, as for `?`. No diagnostic of its own at the hole. |
| Check cache | Unchanged: a namespace with any syntax error has no key (project.rs:606–610) and its outcome is `Failed`. The test-result cache keys on the term's own hash, and a test using a recovered declaration never runs. |
| Importers | Unchanged: skipped with one `E-NAMESPACE-FAILED`, keeping the answers they had when last checked, if their text is the same (live.rs:691–733). Checking them against the recovered signatures is possible later (D2785). |
| Formatter | Refuses any file with an error, now listing all of them, not just the first. `stitchwort fmt` and format-on-save leave the file alone. (D2783.) |
| Language server | Outline, hovers, goals and declaration regions (lsp lib.rs:1548–1552, which lexes strictly today and returns nothing on a lexical error) work on files with errors. `decl_regions` switches to `lex_recovering`. |
| `docs.rs`, `file_imports` | Use `lex_recovering`, so a page or an import list doesn't vanish because of a stray character further down. |

A failed `import` (the other review's F8) stays as now, dropped with its
error. It's a separate small fix: record that the file's imports are
incomplete, and have the elaborator report unknown names in that file as
one note. It's listed as an optional stage below.

## 6. How other systems recover

- **rust-analyzer** never fails to lex or parse. The lexer (`rustc_lexer`)
  marks a bad token instead of stopping: an unterminated string is a string
  token with a flag. The parser wraps tokens it can't use in `ERROR` nodes,
  and stops wrapping at a "recovery set" of tokens for each context, such as
  the item keywords. Our column-0 keywords play that part. A missing piece
  is just an absent child in the tree. In the semantic layer, a missing
  expression becomes `Expr::Missing`, typed as `{unknown}`, and errors that
  involve it are dropped.
- **Roslyn** (C#) inserts zero-width "missing" tokens where one was
  expected, and keeps tokens it skipped as trivia on the next token, so the
  tree still round-trips to the text. Every node can carry diagnostics, and
  the semantic model works on broken trees. Its error types stop the
  follow-on errors.
- **Lean 4**: when a command fails to parse, it records the error and skips
  to the next token that can start a command, which is like our
  column-0 split. Recent versions also elaborate the partial syntax: missing
  pieces become `.missing` nodes, elaborated as a "synthetic `sorry`", whose
  errors are suppressed. So in a tactic proof, you see the goals up to the
  point where the text breaks. (Confidence medium on the details and the
  version they arrived in. The idea, a made-up hole whose errors are
  silenced, is the same as `Missing`.)

All three keep the cause and stop the cascade: one diagnostic for what's
wrong, and a placeholder whose consequences are silenced. Design B does
that with a hole we already have.

## 7. Tests: a corpus of half-typed files

- **The corpus.** `crates/syntax/tests/recovery/`: about 30 small files,
  each one moment of typing. For example: an unclosed `"` in a body, in a
  signature and on the namespace line; a tab; `café`; a BOM midway; an
  unclosed `"""` followed by two declarations; `:=` with nothing after it;
  `rewrite h in` with nothing after it; `| x =>` as the last arm; a
  half-typed arm in the middle of the arms; a broken middle line of a
  `let` block; an unclosed `(` across lines; a half-typed `calc` step; a
  broken `type` (which must fail whole); an indented first line.
  Each has a snapshot that lists, per declaration, kept / signature only /
  dropped, the `Missing` spans, and the diagnostics with their spans.
- **Typing, simulated.** For a sample of the repository's `.sw` files: cut
  one declaration at each token boundary, one at a time, as if it were
  being typed, and check that every *other* declaration parses to the same
  tree as in the full file (`equivalence::shape` per declaration). And
  once the cut is past the `:` of a definition, check that its signature is
  kept. Do the same with a `"`, a tab or a `∀` inserted at random
  positions. This is the test that "an error costs only its own
  declaration".
- **Invariants on every parse**, added to the fuzz test (F7): no panic;
  every span in bounds and on character boundaries;
  the error list is empty exactly when the tree has no `Missing` and the
  strict parse succeeds.
- **One end-to-end test per downstream consumer:** an editor session on the
  example in §4 shows the goal; a project with a lexical error in one file
  keeps that file's namespace; a file with an error is never cached and is
  refused by the formatter.

## 8. Questions for Matt

D2670 and D2690 (recover from lexical errors per declaration) and D2692
(recovery inside a declaration) already have recommendations of yes. These
are the questions those leave open.

- **D2780: recover inside a declaration by keeping its signature and
  putting a hole where the text breaks, which the editor shows as a goal
  (Design B), rather than rebuilding the parser around a lossless tree
  (Design A) or only skipping to the next declaration (Design C)?** [rec:
  B, because it gives the editor what it needs in about five lanes, and
  the hole uses the goal machinery that already keeps unfinished work out
  of the kernel; A can still come later.]
- **D2781: a declaration with a recovered hole counts as an error, never as
  "unfinished", and its goal shows in the editor but not in
  `stitchwort check`'s output?** [rec: yes, because the syntax error is
  the real status, and a goal for text not yet written is noise in the
  terminal.]
- **D2782: no recovery inside `type`, `interface` and `ability`
  declarations: one that breaks fails whole, as now?** [rec: yes, because a
  kept-but-partial data type changes what every match on it means, and
  checking such a type safely needs work in the elaborator that no one has
  asked for.]
- **D2783: the formatter keeps refusing any file with a syntax error,
  rather than formatting the declarations that parsed?** [rec: yes for now,
  because formatting around broken text needs the lossless tree of
  Design A; revisit if format-on-save with errors comes up.]
- **D2784: an unclosed `"""` ends at the next line that starts in column 0
  with a declaration keyword, rather than taking the rest of the file?**
  [rec: yes, because typing `"""` to open a text shouldn't blank every
  declaration after it; it affects only files that are already wrong.]
- **D2785: importers of a namespace with syntax errors stay skipped, rather
  than being checked against its recovered signatures?** [rec: yes for now,
  because it keeps "a namespace with errors" one simple state for the
  cache and the plan; checking against signatures is a separate, later
  question once recovery has been used for a while.]

Decided here, as implementation (say if you disagree): `Expr::Missing` is
a new variant rather than a flag on `Expr::Goal`; the mode fields are
restored by a copy at each recovery point rather than a guard at every
site; tab, no-break space and a midway BOM read as a space after their
error; the strict entry points keep their signatures.

## 9. Tickets to file

In order. Each runs `task test:lane AREA=syntax` plus the tests it names;
lanes 3 and 4 also run `AREA=goals` and `AREA=lsp`. Parser and lexer work is
core language work, so on Opus (D2506).

1. **[Opus, 45 min] Parser groundwork, no behaviour change.** `Modes`
   struct for the eight mode fields; `Parser.errors`; the strict entry
   points fail on a non-empty list. Tests: the existing parser unit tests
   (`task test:lane AREA=syntax`) and `recovery_keeps_good_declarations…`.
   Can start now.
2. **[Opus, 90 min] Lexical recovery** (§3). `lex_recovering`,
   `Tok::Error`, the table's rules, `split_decls` without failure (F11,
   F12), the namespace from the parse in project.rs and live.rs,
   `decl_regions` and `docs.rs` on the recovering lexer. **Absorbs SW-1873**
   and F11 from SW-1918. After SW-1916 (the `${…}` panic) and lane 1.
   Tests: new lexer tests for each row of the table, with good declarations
   before and after; a project test for a file with an unclosed `"`.
3. **[Opus, 90 min] `Expr::Missing`, points 1 and 4** (§4): the node, the
   expression-ran-out insertion, the body-level fallback, the elaborator's
   handling (hole, error status, no diagnostic, no code action, goal for
   the editor only). After lane 1; can run beside lane 2 if the merge is
   handled (both touch `parse_module_recovering`). Tests: the §4 example
   as an editor goal test; a primitive-looking `def f: Nat :=` must not
   be admitted as a primitive.
4. **[Opus, 60 min] Points 2 and 3**: block lines and arms. After lane 3.
   Tests: corpus cases for a broken middle line and a broken middle arm.
5. **[Sonnet, 60 min] The recovery corpus and the typing simulation**
   (§7), and the invariants in the fuzz test. After lane 4. Any surprise
   found is filed, not fixed, unless it's one line. Tests: the new corpus
   test and `task test:one -- fuzz` (its default case count).
6. **[Sonnet, 45 min, optional] A failed import** (the other review's F8):
   record it, and report the file's unknown names as one note. Any time
   after lane 2.

**Not covered here:** incremental reparsing in the language server,
formatting files with errors, and recovery in the `"""` pre-scan itself
(SW-1916's lane). Diagnostics shown while typing (debouncing a parse error
at the cursor) are a language-server display question, for SW-1955's
failure-policy note or its own.
