# Code review: `crates/syntax` (SW-1872)

**Status:** review by reading only, 7 November 2026, Sonnet. Nothing was built
or run, so every claim about behaviour is from the code and is marked with a
confidence. Scope: the lexer, parser, syntax tree, spans, desugaring, layout,
error recovery and messages, `docs.rs`, `equivalence.rs`, `stack.rs`, and the
crate's tests. About 13,200 lines, of which `parser.rs` is 8,876 (5,250 of
code, 3,620 of inline tests).

## Summary

The crate is in better shape than its size suggests. The parts that usually
crash a parser are handled on purpose: recursion is bounded by measured stack
(`E-RESOURCE`, not an abort), chains built by loops are walked and freed
iteratively for `Expr`, the lexer slices only at character boundaries, number
and universe sizes are checked, and a 20,000-case fuzz test runs on every test
run. Parsing is single-pass with no backtracking, so no ambient state can
leak from a failed attempt, and the shared token tests (`negation.rs`,
`record_braces`) keep the parser and formatter from disagreeing. I found no
reachable panic by reading.

What I did find falls in four places. (1) **Recovery stops at the lexer**: one
unterminated string, tab or stray character empties the whole module, which is
the worst moment for the language server (the user is typing). (2) **`Pattern`
was left out of the stack-safety work done for `Expr`**: long tuple and list
patterns build deep trees that drop, and are scanned, recursively, and no test
covers them. (3) **The fuzz test is narrower than it looks**: a fixed seed, no
`"""` text or deep or long inputs, and no time limit, so a quadratic slowdown
would pass. (4) **A few quadratic scans** (`continues_bracket`,
`bracket_depth`, and `equivalence::shape` in the formatter's safety check) that
only show on very large or very deep declarations. Messages have a pattern of
small flaws: the primary label repeats the message, one catch-all message is
stale, and a byte-order mark or invisible character gives a confusing error.
`docs/syntax.md` matches the lexer on every point I checked, but has no grammar
and its Layout section still says "interim".

### Top five recommendations

1. **Recover from lexical errors per declaration** (F1, Opus, M). Emit an error
   token and carry on, so only the declaration with the bad character fails.
2. **Give `Pattern` the same treatment as `Expr`** (F2, Sonnet, S): an iterative
   `Drop`, iterative `has_absurd`/`first_bound`, and a nesting test for long
   tuple and list patterns, run in a child process like the others.
3. **Widen the fuzz test** (F3, Sonnet, S-M): `"""` and `${}` text, BOM and
   odd Unicode, deep and long inputs, a per-case time limit, and the other
   entry points (`lex_with_trivia`, `docs`, the formatter round trip).
4. **Remove the quadratic scans** (F4, F5, Sonnet, M): a prefix-depth array in
   the parser, and a non-pretty or iterative shape in `equivalence`.
5. **Tidy the messages in one sweep** (F6, DeepSeek, S-M): the label that
   repeats the message, "a pattern or `=`", the BOM, invisible characters, and
   "end of the declaration" for an expression.

## Findings

| # | Severity | Confidence | Where | Finding | Fix (size) |
|---|---|---|---|---|---|
| F1 | medium | high | `parser.rs:88-101`, `lexer.rs` | A lexical error (or a first token not at column 0) makes the module empty: one diagnostic, no declarations, no outline, no `failed` names | Error token per bad span; the declaration containing it fails (M, Opus) |
| F2 | medium | medium | `ast.rs:800` (`Pattern`), `parser.rs:349,364,1095,1546` | `Pattern` has no iterative `Drop`; long tuple/list patterns are deep trees walked by unguarded recursive helpers; no test | `Drop` with a work list, iterative helpers, nesting test (S-M, Sonnet) |
| F3 | medium | high | `tests/it/fuzz.rs` | Fuzz: fixed seed; no block text, deep, long or Unicode inputs; no time limit; only `parse_module` | Widen (S-M, Sonnet) |
| F4 | low | medium | `parser.rs:795,835` | `continues_bracket` and `bracket_depth` rescan from the start of the declaration on every call: quadratic for large declarations | Prefix bracket depth, built once (S-M, Sonnet) |
| F5 | low | medium | `equivalence.rs:15-26`, `fmt/lib.rs:118` | `shape` pretty-prints with derived `Debug`: output and stack grow with tree depth (quadratic output for a long `+` chain or a block of thousands of lines); the span-hiding flag isn't restored on panic | Non-pretty or iterative shape; RAII guard (S-M, Sonnet) |
| F6 | low | high | `parser.rs:1589,5247`, `lexer.rs:1150`, `lexer.rs:1125` | Messages: label repeats message; stale "a pattern or `=`"; invisible characters and BOM shown raw | Sweep (S-M, DeepSeek) |
| F7 | low | medium | `lexer.rs:797-950` | Two scanners decide where a `${…}` in a `"""` text ends (`scan_block` pass 1, and the main lexer); they can disagree, and one `expect` relies on agreement | One scanner, or shared skip helper; fuzz cases (M, Sonnet) |
| F8 | low | medium | `parser.rs:140-160` | A failed `import` line isn't recorded like a failed declaration, so its names show as unknown downstream | Record failed imports (M, Sonnet) |
| F9 | low | high | `source.rs`, `lexer.rs` (`as u32`) | No input size limit: spans and columns are `u32` and are cast with `as`; > 4 GiB wraps silently | Fail with `E-RESOURCE` at lex entry (S, DeepSeek) |
| F10 | low | high | `docs.rs:165,174`, `parser.rs:290` | `file_imports`, `docs` and `parse_namespace_line` use `DEFAULT_STACK`, not the session's limit | Take a `stack` argument (S, DeepSeek) |
| F11 | low | high | `parser.rs` (whole file) | 8,876 lines in one `impl`; nine ambient state fields whose invariants are in comments; ~15 separate lookahead scans; 3,600 lines of tests inline | Split by responsibility; tests to `tests/` (M, Sonnet) |
| F12 | low | high | `docs/syntax.md:5-19` | No grammar; "Layout" opens with an "interim rule" the later bullets contradict; layout rules are spread over four places | Write and test a grammar (L: D2671) |
| F13 | low | medium | `parser/sections.rs:117`, `ast.rs:21,763` | Desugared syntax is recognised by name text (`Std.Bool.not`, `%chain…`), so a user-written call of the same name is taken for generated syntax | A flag or variant, not a string (S-M, Sonnet) |

## Details

### F1. A lexical error empties the module (medium, confidence high)

`parse_module_recovering` returns `(Module::default(), vec![d])` when
`lex_with_bars` fails (`parser.rs:88-92`), and the same when `split_decls`
fails (`:100`). The doc comment says so ("A lexical error ... stops
everything"). The recovery that exists (a declaration that doesn't parse is
left out and its names go in `Module::failed`) is per declaration and good, but
it never gets the chance.

Scenario: the user is editing a 600-line file and types `"` in the middle. The
lexer fails at that line's end ("this string isn't closed"), so for the language
server the file has no declarations: no outline, no hover, no diagnostics for
the other 599 lines, and namespaces that import it lose its names. A tab (an
error anywhere), a stray `@`, a `?`-less non-ASCII letter in a name (`café`),
or a BOM does the same. These are the commonest things typed mid-edit.

Fix: let the lexer return the tokens it got plus the errors, with a
`Tok::Error` token (or by skipping to the end of the line) in place of the bad
text; `split_decls` already splits on column 0, so the declaration containing
the error token fails with the lexical diagnostic and everything else parses.
`declared_names_of` already works from tokens. `parse_module` (the strict form)
keeps failing on any error. The unterminated `"""` text is the hard case (it
swallows the rest of the file by definition); there, stop the literal at the
next line that starts in column 0 with a declaration keyword. Question D2670.

Related, in the same place: a first token not at column 0 ("declarations must
start at the beginning of a line") also empties the module; indented text at the
top of a file is rarer, so it can wait.

### F2. `Pattern` isn't stack-safe the way `Expr` is (medium, confidence medium)

`docs/proposals/stack-safe-evaluation.md` records that chains built by loops
(`f a b c`, `1 + 2 + …`, a block's lines) nest as deeply as they are long, and
`Expr` got an iterative `Drop` and an iterative `span()` for that
(`ast.rs:498`). `Pattern` builds the same shapes in loops and got neither:

- `tuple_pattern` (`parser.rs:1095`) folds N components into N nested
  `Pattern::Tuple`; a list pattern `[a, b, c, …]` does the same with `Cons`
  (`:1546`). The parser's `deeper()` check doesn't run for these (it runs per
  call of `pattern()`, not per component folded).
- `Pattern` has no `Drop` impl, so freeing a pattern with 100,000 components
  recurses 100,000 times. A frame is about 50-100 bytes in release, so this is
  5-10 MB: past a 2 MiB test thread, and possibly past the language server's.
  A stack overflow aborts; it can't be caught.
- `has_absurd` and `first_bound` (`parser.rs:349,364`) recurse over the whole
  pattern during parsing, with no guard.
- `Pattern` also derives `Clone` and `Debug`, which the elaborator and
  `equivalence::shape` use.

The nesting tests (`crates/driver/tests/elaboration/nesting.rs`) cover
applications, parentheses, functions, `++` and `+` chains, `let` blocks, list
and text literals and nested patterns (`nested_patterns`, which is depth, not
length). There's no long tuple or list pattern. I did not run one, hence the
medium confidence; the shape of the code is clear.

Fix: add the test first (child process, 100,000 components, like the others).
If it overflows: an iterative `Drop` for `Pattern` modelled on `take_children`
in `ast.rs`; make the two helpers iterative; and check the elaborator's pattern
passes with the same test. Which crate stops the chain (parser limit on
component count, or elaborator guard) is a choice for the lane, as long as the
result is `E-RESOURCE`.

### F3. The fuzz test is narrower than it looks (medium, confidence high)

`tests/it/fuzz.rs` is a good start (git history: `52fa5f007`, `505d5a465`):
mutated examples plus token soup, from a seed, never panicking. What it can't
find:

- **The same 20,000 inputs every run.** `SEED` is a constant, so after the
  first run it adds nothing; `FUZZ_CASES` lengthens a run but not its variety
  over time. A seed taken from the environment (and printed on failure, which
  it already does) would give each CI run new cases.
- **No `"""` text.** `TOKENS` has `${` and `"`, but no `"""`, no `\` followed
  by a newline, and `LITERALS` are all one-line. The block-text scanner
  (`scan_block`, 150 lines, the most intricate lexer code) is reached only when
  a mutation happens to create `"""` from the examples. See F7.
- **No deep or long inputs.** `MAX_LEN` is 64 KiB, the soup is at most 200
  atoms, and the nesting is whatever the examples have. There's no generator
  for 10,000 nested brackets, a 100,000-term chain, or a single line of
  100,000 tokens. The parser's bounded recursion is tested only in the driver.
- **No time limit.** A quadratic scan (F4) or a hang passes as long as it
  finishes. A per-case check in release (say 2 s) would catch both.
- **No stack-overflow detection.** `catch_unwind` can't catch an abort; the
  driver's `nesting.rs` runs each case in a child process for that reason, and
  the fuzz test doesn't.
- **One entry point.** Only `parse_module` runs. `lex_with_trivia`
  (the formatter's lexer), `docs::docs`, `parse_expression` and the formatter
  itself (which re-parses its own output) aren't fuzzed. A property that would
  catch real bugs: for every mutated input the formatter accepts, formatting
  is idempotent and `equivalence::shape` is unchanged.
- **Unicode and encoding.** Non-ASCII appears only if the examples contain it
  (`ℕ`, the aliases). No BOM, NBSP, U+2028, combining marks, NUL or other
  control characters, none of the 1-4 byte boundary cases around a string
  or character literal (`'é'`, `"\u{10FFFF}"`).

### F4. Quadratic scans in the layout helpers (low, confidence medium)

`peek` calls `is_stop`, which for a token that starts a line at or left of the
block's column calls `continues_bracket(i)` (`parser.rs:835`). That folds over
`self.tokens[..i]` from the start of the declaration, to count open brackets.
`bracket_depth(start, i)` (`:795`) does the same from a rule's or guard's start.
`peek_at(offset)` calls `is_stop` once per offset, so a failed `peek` costs
several scans.

The trigger is a line starting with `,` or a closing bracket at the block's
column or left of it, in a long declaration: a long list or record literal in
a block laid out comma-first. Each such line costs O(tokens before it), and
each is looked at several times: 10,000 lines of a comma-first list in a
`let`-block is roughly 10,000 x 5 x 40,000 token visits, a few seconds. The
house style (comma last, closer in column 0) triggers it once per closer, not
per item, so ordinary files don't notice. Large generated tables would.

The parser already builds `matching` (each opener's partner) once per
declaration. A second array, `depth_before[i]` (bracket depth just before token
i), built in the same pass, makes both calls O(1): `continues_bracket(i)` is
`depth_before[i] > 0`, and `bracket_depth(start, i)` is
`depth_before[i] - depth_before[start]`. The two folds count the same thing
(openers minus closers, saturating differently: `bracket_depth` is signed,
`continues_bracket` is too), so the array reproduces both.

Other scans I checked and found linear: `lambda_ahead` and
`lambda_result_type_ahead` skip bracket groups with `matching`;
`line_indent` is O(length of one line), called once per `if` and `calc`;
`sequence_ahead` is bounded by the let's value. A line with 10,000 `if`s
would be quadratic in `line_indent`, but nobody writes that.

### F5. `equivalence::shape` (low, confidence medium)

`shape` formats the module with `{:#?}` after cloning it. Derived pretty
`Debug` indents every nested level by four more spaces, so the output is
O(depth x size): for a chain of N terms it is N^2 characters. A block of 5,000
statements (right-nested `Seq`) writes hundreds of megabytes; a 2,000-line test
a few tens. The formatter runs this twice per module (`fmt/lib.rs:118`) and
`parse_shape` per declaration (`fmt/layout.rs:384,418,1070`), on every
format-on-save. The recursion also uses stack proportional to depth, and
`module.clone()` is the derived recursive `Clone`. None of this matters at the
sizes people write, so it's low, but the formatter's safety net failing on a big
generated file is the wrong failure.

Also: `HIDE_SPANS` is toggled with `replace(true)` and put back after
(`equivalence.rs:20-25`); a panic in between leaves the thread-local set, and
every later `Span` debug print on that thread shows `_`. Use a drop guard.

Fix: print with `{:?}` (one line, O(size)) or, better, write the comparison as a
small explicit-stack walk that returns the first difference (which the
formatter's error message wants anyway: "names the first difference").

### F6. Message flaws (low, confidence high)

- **The label repeats the message.** `error()` in `parser.rs:5247` and
  `lexer.rs:1150` sets the message as both the diagnostic's message and its
  primary label's text. The rendered output (snapshot
  `running__examples__reject__keyword-let-name.snap`) shows it twice, as the
  header and under the caret. Most `E-PARSE` errors do this. The label should
  say what is at the caret ("found `with`") or be empty.
- **Stale catch-all.** `pattern()` ends with `unexpected_name("a pattern or
  `=`")` (`parser.rs:1589`), left from the equation syntax. It shows for
  `let with := n + n`, where `=` is wrong (the separator is `:=`), and for a
  lambda or arm. The caller should say what it wants.
- **Invisible characters.** `unicode_error` prints the character itself
  (`unexpected character `…``): for U+FEFF (a BOM, which Windows editors add),
  NBSP, U+2028 or a control character, the message looks empty. The ASCII path
  prints `c as char`, raw for a control byte. Print `U+FEFF` for anything that
  isn't a visible glyph. A leading BOM should just be skipped: nothing in the
  repo strips it (I searched), and the run-time tests that mention U+FEFF are
  about `Text`, not source.
- **"Declaration" in an expression.** `Parser::unexpected` says "reached the
  end of the declaration" (`:1018`) and `finish` "the end of the declaration"
  (`:1179`), also when parsing a REPL or `--at` expression
  (`parse_expression`). "the end of the input" would do for both.
- **Only the first error of a declaration** is reported (the parse aborts at
  the first). That is a fine trade for no cascades, but it means two typos in
  one definition take two edit-check cycles. Not a change I'd make; I note it
  as the design.

### F7. Two scanners for `${…}` in a `"""` text (low, confidence low-medium)

`scan_block` (lexer.rs:797) first finds, for the whole `"""` text, where each
`${…}` ends, by its own scan (it skips one-line `"…"` and `'…'` literals so a
`}` inside them doesn't count), so it can remove the common indentation. The
main lexer then lexes the contents of each `${…}` again as ordinary tokens
and ends it at the first `}` of brace depth 0 it sees (`:576-610`), taking the
next precomputed piece. The two must find the same `}`. The code relies on it:
`pieces.pop_front().expect("a block's last piece closes it")` (`:591`).

I could not make that `expect` fire (a disagreement mostly ends in "this
string isn't closed"), but two cases look wrong:

1. In the skip of a one-line literal inside `${…}`, `i += if b == b'\\' { 2 }
   else { 1 }` (`:867`) can step over a newline after a backslash, so the
   "stays on one line" error is bypassed and `line_starts` misses a line. The
   main lexer then reports "this string isn't closed", with a misleading span.
2. A nested string that itself contains `${` and `}` and a `}` in a literal,
   `"""` + newline + `${ "a${ "}" }b" }`: the pre-scan stops the outer
   interpolation at the first `}` it meets after skipping `"a${ "`, which is the
   one inside the inner `"}"` literal. The main lexer closes the outer at the
   real end and then resumes after the pre-scan's `"""`, so the text between is
   never lexed and there's no error: silently wrong. This is contrived, and
   is from reading, not running.

Fix: one scanner. Either lex the interpolations with the main lexer and
de-indent the text pieces afterwards, or move "where does this `${…}` end"
into a function both use. Add the cases above and `"""` generators to the fuzz
test (F3).

### F8. A failed import isn't recorded (low, confidence low)

A declaration that fails to parse puts its names in `Module::failed`, so uses of
them don't cascade into "unknown name". An `import` that fails
(`parser.rs:152-160`) is just dropped: no record of which names it would have
brought in. While the user types `import Std.Li` the names from it show as
unknown everywhere in the file. I did not check whether the driver suppresses
unknown-name errors in files with syntax errors; if it does, this is moot.
Fix: record a `failed_imports` flag or the path, and have the elaborator treat
unknown names as probably-from-it (one note, not one error per use).

### F9. No input size limit (low, confidence high)

`Span` is `{ file, start: u32, end: u32 }`, and the lexer builds them with
`start as u32` (about thirty places). `Span::new` has only a `debug_assert!`.
A source over 4 GiB wraps silently in release. D2543 says limits fail rather
than choose. Nothing in `driver`, `host` or `cli` limits a source's size (I
searched for it), so the lexer is the right place: if `text.len() > u32::MAX`,
return `E-RESOURCE` once, and the `as u32`s are then safe. (A related small
thing: a number literal is parsed with `str::parse::<BigUint>`, which is
quadratic in its digits, so a megabyte of digits takes seconds. It is the
user's own file; not worth a limit by itself.)

### F10. `DEFAULT_STACK` in three entry points (low, confidence high)

`parse_namespace_line` (`parser.rs:290`), `docs::file_imports` and `docs::docs`
(`docs.rs:165,174`) and `equivalence::parse_shape` use `DEFAULT_STACK` (1.5 MiB
"safe on a 2 MiB thread"), while the driver passes the session's limit to the
others. They are called from the language server and the CLI on session
threads, which is fine today because the threads are larger; but the point of
`Limits::stack` is that the number comes from the thread, and these three don't
follow it. A smaller thread (or the limit lowered for a test) would give a
stack overflow, not `E-RESOURCE`. Add a `stack` argument or use the session's.

### F11. Size and shape of `parser.rs` (low, confidence high)

The 1 Nov review (section 4.4) listed `syntax/parser.rs` at 7,699 lines and
suggested splitting expressions, patterns, layout and recovery. Since then
`parser/declarations.rs` (885) and `parser/sections.rs` (329) were split off,
but the file grew to 8,876. Of the rest, 3,620 lines are `mod tests` (149
tests) in the same file, so every parser edit recompiles and re-reads them.

What makes the file hard to reason about is not its length but the **ambient
state**: `limit`, `allow`, `calc_depth`, `rewrite_rule`, `rewrite_at`,
`guard_start`, `let_value`, `in_list` (and `matching`). Each changes how
`peek` and `is_stop` behave, each is set and restored by hand around a call
(`block`, `guard`, `rewrite_body`), and the rules for how they combine are in
comments. It works because the parser is single-pass and a failed declaration's
parser is discarded, so a missed restore on an error path can't leak; but a
future `try`-style parse (backtracking, or the incremental reparse the language
server would like) would meet stale state. Group them in one struct with
`with_*` methods that restore on every path.

The cursor/layout methods (`peek`, `is_stop`, `continues_*`, `*_ahead`,
`line_indent`; about 800 lines) are the natural first module. Expression,
pattern and block/statement code follow. Mechanical, so DeepSeek or Sonnet;
it will conflict with any other lane touching the parser, so schedule it alone.

### F12. Syntax and documentation (low, confidence high)

I checked the lexical claims in `docs/syntax.md` against the lexer: ASCII names,
no tabs, the Unicode aliases and their ASCII forms, escapes (including
`\u{…}` limits and the surrogate error), `"""` text rules, the `--|` doc
comments, `..<`/`..=`, the negative-numeral rule, the leading-operator rule.
All agree. The guide audit (`SW-1850-guide-accuracy.md`) already lists the
errors in `syntax.md`; I don't repeat them.

What is missing is a grammar. `syntax.md` is a long set of rules by topic,
and:

- Its first section, "Layout", says "Interim rule, until the full layout
  specification (DESIGN.md section 14): every following line that's indented
  continues it" (`:5-19`). The real rules (block column, `then`/`else` and `|>`
  at the block's column, leading infix operators, brackets continuing lines
  in column 0, the column-0 split in `split_decls`) are bullets 14-17 of the
  same list, lines 331-338, line 403 and line 1892. A reader has to assemble
  them; the parser's `split_decls` comment is the best summary.
- DESIGN.md section 14 asked for "a short written spec of the indentation rules
  ... backed by golden parsing tests". The nearest thing is
  `tests/it/layout.rs` (generated round trips), which checks the rules
  without stating them.
- Two other consumers keep their own copy of the grammar: the formatter
  (token-level rules) and the editor highlighters (keywords; SW-1281 made that
  one list, with a test). The parser is the only authority.

Recommended: a grammar chapter (EBNF for expressions, patterns, declarations,
plus a layout section stated as rules about `Token::column` and `line_start`),
and a test that every grammar production's example parses. Direction, so a
question: D2671.

### F13. Desugared syntax recognised by name (low, confidence medium)

The parser builds syntax for sugar and the later passes recognise it by text:
`Std.Bool.not` and `Std.Iff` in `leftmost_child` (`sections.rs:117`), the
`%chain` prefix for a comparison chain's hidden binder (`ast.rs:21,763`,
`parser.rs:4973`), `SECTION`, `%left`/`%right`, and `Std.Show.toText`
for interpolation. The `%` names are safe (the lexer can't produce `%` in a
name, so no capture). The `Std.` ones are not distinct from what the user can
write: `leftmost_child` treats a user's `Std.Bool.not x` as the generated
negation. Hardly ever matters, but the stringly typing is also why
`equivalence::renumber_chains` has to rewrite offsets in a Debug string.

## The tree and node ids (question 4 in the brief)

Could the tree carry ids cheaply? Yes, for `Expr::Field`, as
`docs/proposals/syntax-node-ids.md` plans, and with caveats I'd add to it.

- **Size:** `Expr` is 88 bytes (the proposal's measurement), `Field(Box<Expr>,
  Name)` uses 48 of them, and `Name` (`String` + 12-byte `Span`) has 4 bytes of
  tail padding. A `u64` in `Field` is free; a `u32` could sit in `Name`'s padding,
  but 32 bits wrap in a long-lived server (a keystroke reparses; a day is
  millions of nodes), and a wrap that reuses an id is the hazard being removed.
  Use `u64`.
- **`Clone`:** `Expr` derives `Clone`. A derived clone copies the id, so a
  `.clone()` (about 300 in `elab`) gives two live nodes the same id, which is
  the reverse of "a copy gets a new number". The id needs its own type with
  `impl Clone` that takes a fresh number. This is the easy thing to miss.
- **`Debug`/equality:** `equivalence::shape` prints the tree; the id type
  must print `_` under `HIDE_SPANS` or every shape differs.
- **Hashing/caching:** nothing in the syntax crate hashes the tree, so ids
  don't touch cache keys; confirm that no `elab` cache serialises `Expr`.
- **All nodes, not just `Field`:** every variant would need the field (about
  50). A cheaper general route is to give desugared nodes distinct spans and key
  by `(file, start, end)`, but the proposal found generated syntax shares spans,
  so that doesn't give identity.
- **Parallel parsing:** a global counter makes ids differ run to run; fine for
  equality keys, but not as sort keys.

The other desugarings in the parser (`bind_let`'s one-arm `Match`, comparison
chains, `%left`/`%right` operator sections, string interpolation, `Pipe`,
`Seq`, list patterns to `Cons`) build only from parts with real spans, with
`Span::NOWHERE` only as a temporary in `mem::replace`, so none of them creates a
node that the elaborator could key by address except through the cloning already
described in the proposal.

## Parser and formatter duplication

Small and managed. `negation.rs` is the one list of tokens that close an
operand or open an atom and the `-`/`!` rules, shared on purpose;
`record_braces` is shared (`pub`, documented as used by both); the keyword table
is one macro. The formatter re-lexes and re-parses its output and compares
shapes (F5), so duplicated knowledge shows up as `Error::Internal` rather
than wrong output. What the formatter does keep separately is its spacing table
(`fmt/spacing.rs`), which is a presentation concern, and `fmt/layout.rs`'s
bracket-conversion rules, which restate the parser's bracket continuation
(column-0 `,`/closer) rule. That last one is the only duplication I'd watch:
the rule is in `split_decls`, `continues_bracket` and the formatter.

## Checked and sound

- **Stack bound.** `deeper()` runs in `expr`, `append_expr` (right-recursive
  `++`), `unary` (prefix `-`/`!`) and `pattern`. `stack.rs` measures real
  address distance, so one byte limit fits debug and release. Frame size is
  protected by `#[inline(never)]` helpers and a benchmark; `Result` is boxed
  for that reason (`parser.rs:25-37`). The limit comes from the session
  (`Limits::stack`) in the driver's parse calls.
- **Chains.** `add_expr`, `mul_expr`, `app`, `pipe_chain`, `logic_chain`
  (collects operands, then folds) and `tuple_expr` are loops; `Expr::span` walks
  chains in loops; `Expr::Drop` is a work list. Tested to 100,000 in
  `nesting.rs` (except patterns: F2).
- **Lexer.** Every `text[i..]` slice starts at an ASCII byte or after a
  `len_utf8()` step; the `.expect("non-empty")`s follow a length check;
  `\u{…}` is range-checked and surrogates are refused; a `'` or `"` at the end
  of the file gives an error; `\r\n` is handled; a BOM is not (F6); an empty file
  and a file of comments give an empty module. `ident'` and `x.y` rules are
  consistent with the docs.
- **Parser indexing.** `self.tokens[...]` appears at a few places, each after a
  `peek` or length check (`prev_span` after consuming a token;
  `definition`'s `tokens[pos]` after `peek` saw the keyword). No backtracking
  (`self.pos =` appears nowhere), so no loop can revisit a token; loops that
  don't consume (`while self.peek() != Some(&Tok::Colon)` in `definition`) end
  in an error at the end of the tokens.
- **Numbers.** `Tok::Num` is a `BigUint`, so no overflow; `Type n` is
  `try_from` plus `MAX_UNIVERSE_LEVEL`; ranges and sections don't compute with
  the values.
- **Recovery.** Declaration split at column 0 with keyword protection (an
  unclosed `{` doesn't swallow the file), attribute-only groups attach to the
  next declaration, `declared_names_of` finds names by tokens, duplicate
  namespace / late namespace / late import are errors that don't abort the
  rest. `recovery_keeps_good_declarations_and_names_the_broken` covers the
  main path (only three recovery tests in all; see tickets).
- **Hidden names.** `%chain`, `%left`, `%right` can't be written, so no capture;
  generated references use absolute `Std.` names.
- **Doc comments.** `docs.rs` slices only at spans the lexer produced; `link_ranges`
  advances past each match; `summary` indexes guard their bounds.
- **Span math.** `Span::to` takes min/max; `Span::point(eof)` is used for errors
  at the end.
- **Equivalence of the sharing.** `closes_operand`/`opens_atom` are one list for
  parser and formatter, with a header saying so.

## Status of the 1 Nov review's findings in scope

| Finding | Status |
|---|---|
| 4.4 `syntax/parser.rs` is 7,699 lines; decompose by responsibility | **Open, partly done.** `parser/declarations.rs` and `parser/sections.rs` split off; the file is now 8,876 lines, 3,620 of them tests (F11). |
| Parser errors and structured resource errors named as good examples of bounded failure | **Still true** (`E-RESOURCE` from `deeper`); gaps: `Pattern` (F2), size (F9), three entry points (F10). |
| 1.2 Test fingerprint covers `syntax` sources | In scope only as a user: `build.rs` hashes `crates/syntax`, still the case; the finding itself is about `rt`. |

## Tickets to file

Grouped as lanes of 30-90 minutes. Parser changes are core language work, so
Opus where noted (CLAUDE.md, D2506).

1. **[Opus, 90 min] Lexical error recovery** (F1, D2670). `Tok::Error` or skip to
   end of line; strict `parse_module` unchanged; tests in `parser.rs` for: an
   unterminated string, a tab, a stray `@`, `café`, a BOM, each with good
   declarations before and after; the language-server outline test. Includes the
   `"""` rule (end an unclosed text at the next column-0 keyword). Also F8 if
   cheap.
2. **[Sonnet, 45 min] `Pattern` stack safety** (F2). Nesting test first (child
   process, 100,000 tuple components and 100,000 list items); then iterative
   `Drop`, `has_absurd`, `first_bound`; elaborator pass check.
3. **[Sonnet, 60 min] Fuzz test widening** (F3, F7's cases). Seed from env (printed
   on failure), `"""`/`${}`/BOM/Unicode/deep/long generators, per-case time
   limit, run `lex_with_trivia`, `docs`, and the formatter's idempotence and
   shape-preservation on accepted inputs. Findings go to tickets, not fixes.
4. **[Sonnet, 60 min] Quadratic scans** (F4, F5). `depth_before` array in the
   parser; `equivalence::shape` as `{:?}` or an explicit-stack walk with the
   first difference; RAII guard for `HIDE_SPANS`. Add a timing test with
   a 20,000-line comma-first list.
5. **[DeepSeek, 60 min] Message sweep** (F6, F9, F10). Label text that adds
   information; "a pattern or `=`" per call site; BOM skipped; `U+XXXX` for
   non-printing characters; "the end of the input" for expressions; `E-RESOURCE`
   past `u32::MAX` bytes; `stack` argument on the three entry points. Snapshots
   regenerate.
6. **[Sonnet, 90 min] Split `parser.rs`** (F11). Cursor/layout module first, then
   expression, pattern, block; tests to `crates/syntax/tests/`; group the
   ambient state. Schedule alone (conflicts with every syntax lane).
7. **[Sonnet, 45 min] One `${…}` scanner for `"""` text** (F7), after ticket 3 so
   the new cases exist first.
8. **[Opus, 90 min] A grammar chapter** (F12, D2671), after the split.
9. **[Sonnet, 30 min] Desugared syntax without name matching** (F13), together
   with the node-id work (`syntax-node-ids.md`; note the `Clone` and `Debug`
   points above when that is implemented).

## Questions for Matt

- **D2670: recover from lexical errors per declaration?** Today any lexical
  error (an unclosed `"`, a tab, a BOM, `café`) leaves the file with no
  declarations at all, which blanks the language server's outline, hover and
  diagnostics for the whole file until it is fixed. The change makes only the
  declaration containing the error fail. [rec: yes; it is the language-server
  behaviour you'd expect, and the strict `check` result is unchanged]
- **D2671: write a grammar for the language?** `syntax.md` is by topic, its
  Layout section says "interim", and the parser is the only specification.
  A grammar chapter (EBNF plus the layout rules stated on columns), with a test
  that its examples parse, would also be the brief for a second implementation
  or an editor grammar. It costs a lane after the parser split. [rec: yes, after
  the split]
