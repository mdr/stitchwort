# Code review: `crates/syntax` (SW-1883, Opus, independent)

**Status:** review by reading only, 7 November 2026, on `lane/SW-1883`
(= `main` at e9a294445). No code was built or run: every scenario below is
traced by hand through the source, and says so where that matters. Scope:
the lexer, the parser (`parser.rs`, `parser/declarations.rs`,
`parser/sections.rs`), the syntax tree (`ast.rs`), spans and sources,
desugaring, layout, error recovery and messages, `docs.rs`,
`equivalence.rs`, `negation.rs`, `stack.rs`, and the crate's tests.

## Summary

The parser is careful in the places that have been hit before. Its stack
limit measures real stack use, so the same limit works in debug and release
builds. Chains such as `f a b c`, `a + b + …` and `&&` are built in loops,
and `Expr` has a drop that doesn't recurse. The keyword table is the only
list of keywords. The negation rules and `record_braces` are shared with the
formatter, so the two can't disagree about them. Slicing on byte offsets is
almost always at an ASCII byte or after `len_utf8`, so it is safe.

Three things are weaker than they look, though:

- **One reachable panic.** It is in the lexer's `"""` text with `${…}`,
  where two scanners read the same text differently.
- **Recursion the stack limit doesn't see.** The parser counts its own
  recursion, but several passes after it recurse over trees it built in
  loops. A long comparison chain, a long list or tuple pattern, or the
  formatter's tree comparison can each overflow the stack. An overflow
  aborts the process; it isn't an error.
- **Recovery isn't fit for the editor.** Recovery works per declaration,
  but a lexical error, including a byte-order mark, gives an empty module.
  The namespace fallback fails on the same text, so the file drops out of
  its project.

The fuzz test, which ought to catch all three, mostly tests the lexer's
handling of tabs.

**Top five recommendations**

1. Fix the `"""`/`${` disagreement (F1). Check that the main lexer's `}`
   is where the pre-scan put it, and give an error otherwise. Add the
   repro as a test. S.
2. Make lexical errors recoverable (F2): an error token, with lexing going
   on at the next line. Also make `parse_namespace_line` lex only the head
   of the file, and skip a leading byte-order mark (F6). M.
3. Put every recursive pass after the parser under the stack limit, or
   rewrite it as a loop (F3, F4): `chain`'s `go`, `exists_chain`,
   `has_absurd` and `first_bound`, plus a non-recursive drop for `Pattern`.
   Add nesting tests for each. M.
4. Replace `equivalence::shape`'s `Clone` plus `{:#?}` with a comparison
   that walks the tree in a loop and skips spans (F5). Today the formatter
   pays recursion that grows with the tree's depth, and output that grows
   with its square. M.
5. Rework the fuzz test (F7). Don't let tabs end nearly every case in the
   lexer. Generate `"""` texts, Unicode, long chains and deep nesting. Run
   it on a thread with a known stack. Check that every span is in range and
   on a character boundary, and fuzz the other entry points too. M.

**Count:** 2 high, 6 medium, 9 low.

## Findings

| # | Where | What | Sev | Conf | Size |
|---|---|---|---|---|---|
| F1 | lexer.rs:835–870 vs 586–615 | `"""` pre-scan and main lexer disagree on where a `${…}` ends; the lexer jumps backwards, giving a span with start > end and a slice panic in release | high | medium (traced) | S |
| F2 | parser.rs:83–93, 289–293; driver project.rs:792 | Any lexical error empties the module, and the namespace fallback fails too, so the file leaves the project and its importers fail | high | high | M |
| F3 | parser.rs:4964–5031 | `chain`'s `go` recurses once per operand of `a < b < c < …`, outside `deeper()` | medium | high | S |
| F4 | parser.rs:349–385, 1104–1112, 1534–1541; ast.rs:800 | Long list and tuple patterns build trees as deep as they are long, in a loop; `has_absurd`, `first_bound` and the derived drop of `Pattern` recurse over them | medium | high | S |
| F5 | equivalence.rs:16–28 (fmt lib.rs:118, layout.rs:384–418, 1062) | `shape` is a derived `Clone` plus `{:#?}` of the whole module: recursion as deep as the tree, output that grows with the square of the depth | medium | medium | M |
| F6 | lexer.rs:571–579, 1125–1140, 350 | A byte-order mark is an error with an invisible character in the message, and through F2 it empties the file; no-break and zero-width spaces read the same way; CR-only line endings read as one line | medium | high | S |
| F7 | tests/it/fuzz.rs | The fuzz test mostly exercises the lexer's tab error; it never generates `"""` texts, deep or long inputs or unusual Unicode, and it checks nothing about spans | medium | high | M |
| F8 | parser.rs:83–93 (design) | Recovery drops a whole declaration, so a half-typed theorem loses its goals and hovers; manual save and restore of eight parser mode fields is a hazard for any finer recovery | medium | high | L |
| F9 | parser.rs:835–848 | `continues_bracket` scans the declaration from its start on every `peek` at a line-leading `,` or closer: quadratic in the leading-comma layout that docs/syntax.md recommends | low | high | S |
| F10 | parser.rs:2212, sections.rs:104–147 | Two more quadratic spots: `defs.insert(0, …)` per local definition, and `span()` per level in `leftmost_child` | low | high | S |
| F11 | parser.rs:405–490 | Tokens before the first group (a file starting with a column-0 `:=`) are parsed by nothing and reported by nothing | low | high | S |
| F12 | parser.rs:406–414 | An indented first token fails the whole file with one error | low | high | S |
| F13 | parser.rs:5079–5100, 5044–5077, 5116–5134, 4645 | Desugaring marks compiler-written names inconsistently (empty span or not), and several nodes share one span | low | high | S |
| F14 | ast.rs:498–720 | `has_nested` and `take_children` must list every boxed child by hand; a forgotten one quietly brings back the recursive drop | low | medium | S |
| F15 | parser.rs (8,876 lines) | Size: 3,600 lines of inline tests; the layout oracle `is_stop` and eight mode fields; a `parser` → `docs` → `parser` cycle | low | high | M |
| F16 | lexer.rs:96–107, 136–138 | Stale token docs: `match … \| p -> …`, `return x -> …`, `let x = e`, `get () => k -> …` | low | high | S |
| F17 | docs/syntax.md:11, 1454–1520 | Layout says a `--` run is a doc (against SW-1044); the "loosest first" table puts `!a` after application, and has a pattern row | low | high | S |

## Details

### F1. The `"""` pre-scan and the lexer disagree about `${…}` (high)

A `"""` text is scanned twice. `scan_block` (lexer.rs:797) runs first,
removes the indentation, and records each `${…}` range. To find the range's
`}`, it skips one-line strings and character literals using its own rules
(lexer.rs:835–870). The main loop then lexes the expression inside the
`${` with the real lexer. At the `}` that closes it (lexer.rs:586), it pops
the next precomputed piece and sets `i = stop + 2` or `stop + 3`, trusting
that both scanners found the same `}`.

They can disagree in at least two ways:

- **A quote after a digit.** The pre-scan treats `'` as starting a
  character literal only when the byte before it is not alphanumeric, `_`
  or `'`. The lexer ends a number at the `'`, so in `1'}'` the lexer sees
  `1` and then the character `'}'`. The pre-scan sees no literal and closes
  the `${` at that `}`.
- **A nested interpolated string holding a quote**, as in `"${"}"}"`. The
  pre-scan's string skip stops at the first `"`, but the real lexer reads
  the nested `${…}`.

If the pre-scan closes early and a later `${` sits on the same line inside
a nested string, the lexer's `i` moves backwards. This was traced by hand
through the code, not run:

```
def t: Text := """
  ${1'}' ++ "${x}"}
  """
```

Relative to the `$`, the pre-scan records `${` ranges at 0–4 and 10–13.
The lexer reads `1`, `'}'`, `++` and the nested string `"${x}"`. At the
final `}` (offset 15) it pops the piece whose `stop` is 10, so
`text_start` = 16 and `i` = 12. Then:

- `Span::new(16, 12)` fails its `debug_assert` in debug builds and in
  tests.
- In release, `text[text_start..stop]` (lexer.rs:608) is `text[16..10]`,
  which panics.

The language server calls the lexer on its main thread (`lens.rs:23`,
`lib.rs:1551`, `lib.rs:1644`) and on its checker thread, whose panic ends
checking. So typing this input stops the server. The fuzz test can't find
it (F7).

**Fix (S).** In the `}` branch for a block, compare `text_start - 1` with
the end that the pre-scan recorded. If they differ, return `E-PARSE`, "this
`${…}` can't be read: …". That is cheap and turns every disagreement into
an error. A fuller fix would let the real lexer find the `${…}` ends, with
the pre-scan only finding the line starts and the closing `"""`. Either
way, add the repro and the `"${"}"}"` variant as lexer tests.

### F2. One lexical error loses the whole file (high)

`lex_keeping` returns at its first error. `parse_module_recovering`
(parser.rs:90–93) then returns `Module::default()`, with no namespace, no
imports and no declarations. Every lexical error does this:

- a tab;
- an unclosed `"`, `'` or `"""`;
- a stray `$`, `@` or `∀`;
- a non-ASCII letter in a name;
- an unknown escape;
- a byte-order mark (F6).

Because of that:

- **The editor loses the whole file**, not just the broken declaration.
  The driver skips elaboration when the module is empty
  (`driver.rs:674–677`), so diagnostics, hovers, goals, lenses and decl
  regions (`lsp/lib.rs:1551`) all go. Most of these errors are momentary
  while someone types, such as an opening `"` or `'` before its partner.
- **The project loses the file.** `project.rs:792` falls back to
  `parse_namespace_line`, which lexes the whole text again
  (parser.rs:291) and fails on the same error. The file is then dropped
  (`continue`), and every file that imports its namespace reports it as
  missing. So one bad byte cascades across files.

Recovery is easy here because a lexical error can't span lines: strings,
characters and `${…}` are all single-line, and a `"""` error is about its
opening line or the end of the file.

**Fix (M).**

- Add a `Tok::Error`. Record the diagnostic, skip to the end of the line
  (or of the bad character), and carry on.
- Let `split_decls` and the parser treat a group holding a `Tok::Error`
  as failed, with its names recovered as now. An unclosed `"""` still
  takes the rest of the file, which is the right reading.
- Make `parse_namespace_line` lex only up to the first newline that is
  followed by a column-0 token other than `namespace`, or stop at the end
  of the first group. A broken body then can't hide the file's namespace.

D2690 asks whether to do this.

### F3. A long comparison chain overflows the stack (medium)

`comparison_chain` collects its operands in a loop, and each operand goes
through `append_expr`'s `deeper()` at a shallow depth. Then `chain`
(parser.rs:4964) folds them with `Chain::go`, which calls itself once per
operand, with several `Expr`s (88 bytes each) in each frame, and doesn't
check the limit. Writing `0 < x < x < … < x` with tens of thousands of
operands passes the parser's own check and then overflows, which aborts
the process.

`exists_chain` (parser.rs:5044) has the same shape: it recurses once per
typed parameter of the lambda after `exists`.

**Fix (S).** Build the chain from the right in a loop. The `let`s and
`&&`s nest right, so a reversed loop that carries `rest` works.
`exists_chain` can work the same way. Add `long_comparison_chains` to
`driver/tests/elaboration/nesting.rs`, with `just_past_the_limit`.

### F4. Long patterns are as deep as they are long (medium)

`[p1, p2, …, pn]` (parser.rs:1534–1541) and `(p1, …, pn)`
(parser.rs:1104–1112) are collected in a loop and folded into nested
`Cons` and `Tuple` nodes n deep, so `deeper()` never sees the depth. Then
three things recurse once per level, with nothing to stop them:

- `has_absurd`, which `arm` calls on every arm's patterns
  (declarations.rs:676);
- `first_bound`, called on or-patterns;
- `Pattern`'s derived drop (`Expr` has the non-recursive drop, `Pattern`
  doesn't).

The existing `nested_patterns` test covers `(Cons _ (Cons _ …))`, which
the parser does recurse on, but not the flat forms.

**Fix (S).** Write `has_absurd` and `first_bound` with an explicit stack,
or check `self.stack` inside them. Give `Pattern` the same `Drop` as
`Expr`. Add `long_list_patterns` and `long_tuple_patterns` to the nesting
tests. The elaborator's pattern compiler may need the same treatment, but
that is outside this crate.

### F5. The formatter's tree comparison grows with the square of the depth (medium; confidence medium)

`equivalence::shape` clones the module, which is a recursive derived
`Clone`, and prints it with `{:#?}`, a recursive derived `Debug` with
pretty indentation. The formatter calls it on every file it formats
(`fmt/lib.rs:118`). For per-declaration checks it reparses and calls it
again on every trial edit (`layout.rs:384–418`, `same_decl`).

Two costs follow:

- **Recursion.** Loop-built chains (a long sum, a 2,000-line block, which
  nests its `let`s 2,000 deep) are as deep as they are long. `Debug`
  recursion takes several frames per level, so it can overflow where the
  parser didn't. Whether that happens below the elaborator's own limits
  isn't measured.
- **Output size.** Pretty `Debug` indents each level further, so the
  string grows with the square of the depth. Roughly, a 2,000-`let` block
  prints lines that average thousands of spaces, about 10⁸ bytes. This
  estimate is from reading the code, not measured.

**Fix (M).** Replace `shape` with an equality between two trees that walks
both in a loop with an explicit stack, ignoring spans, `arm` and the
`%chain` offsets (renumbered as now). Alternatively, hash the tree in a
loop. Keep `shape` for test output only.

### F6. Invisible characters and line endings (medium)

- **Byte-order mark.** U+FEFF at offset 0 goes to `unicode_error`
  (lexer.rs:578): "unexpected character ``", with an invisible
  character between the backticks. Then F2 empties the file. Some Windows
  editors write a byte-order mark by default. Nothing in `crates/` strips
  it: grepping for `feff` finds only JS and extraction code and tests.
- **Other invisible characters.** U+00A0 (no-break space, common in text
  pasted from the web), U+200B (zero-width space) and U+2028 (line
  separator) give messages that show nothing between the backticks.
- **Line endings.** `\r` is whitespace anywhere (lexer.rs:350). A file
  with CR-only line endings is one line, so every declaration after the
  first continues the first, giving one confusing error. CRLF is handled
  correctly.

**Fix (S).**

- Skip a leading U+FEFF, as Rust and Go do. D2691 asks whether to.
- For a whitespace, control or format character, write the message as
  "unexpected character U+00A0 (no-break space)". The name can come from a
  short table, or just give the code point.
- Treat a `\r` not followed by `\n` as an error ("old Mac line endings"),
  or as a newline.

### F7. The fuzz test misses what it is for (medium)

`tests/it/fuzz.rs` claims the lexer and parser never panic. In practice:

- **Soup cases are lexer tests.** After each atom, one time in six
  `soup` appends `\t` (fuzz.rs:183), which is always a lexical error. With
  up to 200 atoms (100 on average), the chance of no tab is about
  (5/6)¹⁰⁰ ≈ 10⁻⁸. The literals `"unterminated`, `''`, `'ab'`, `\` and
  `ℕ` are lexical errors too. So half the cases end in the lexer and never
  reach the parser.
- **No `"""`** is in the generators, so F1's class is reachable only from
  a corpus file that already has one.
- **No long or deep inputs** are generated (F3–F5), and an overflow aborts
  the test binary rather than failing a case. `catch_unwind` can't catch
  it, and the case isn't named.
- **No Unicode** apart from `ℕ`: no byte-order mark, no-break space,
  zero-width joiner, combining marks or CR-only line endings.
- **No checks on what comes back.** Every diagnostic's spans should be
  in the file's bounds, with start ≤ end and both on character boundaries.
  Renderers slice with them, so a bad span is a panic waiting downstream.
- **One entry point.** Only `parse_module` is fuzzed. `lex_with_trivia`
  (the formatter and LSP path), `parse_namespace_line`,
  `parse_expression`, `decl_ranges`, `docs::docs`, `file_doc` and
  `record_braces` aren't.

**Fix (M).**

- Make soup's separators mostly spaces and newlines, with a tab rarely,
  and add a soup made only of valid tokens.
- Add `"""` blocks with `${…}` and quotes to the literals.
- Add a generator for long chains (`<`, `+`, `&&`, `|>`, list and tuple
  patterns) and deep brackets.
- Run each case on a spawned thread with a fixed stack, so an overflow is
  at least in a known place.
- Assert the span invariants on every diagnostic.
- Call the other entry points on the same text.

### F8. Recovery works only per declaration (medium, design)

A declaration that fails to parse is dropped whole, with its names put in
`Module::failed`. For the editor that means:

- a theorem with one half-typed line loses every goal and hover in it;
- a 200-line `def` loses its signature, so the uses of it elsewhere lose
  their types too.

The parser's mode fields make finer recovery risky as things stand. There
are eight of them: `limit`, `allow`, `calc_depth`, `rewrite_rule`,
`guard_start`, `rewrite_at`, `let_value` and `in_list`. Each site saves
and restores them by hand, usually as `let saved = …; let r = …; restore;
r?`. That is correct today only because an error abandons the whole
declaration, so nothing leaked on an error path is ever read. A recovery
point inside a declaration would read whatever state the failed path left
behind.

**Recommendation (L, a design note first).** Recover the signature when
the body fails, as `Decl::Signature` with a hole for the body. Recover at
the next arm `|` at the arms' column. Before either, put the mode fields
behind one helper that restores on every path (a closure, or a guard
value).

### F9. Leading commas are quadratic (low)

`is_stop` runs on every `peek`. For a token that starts a line at or left
of the block's column and is a `,` or a closer, it calls
`continues_bracket`, which folds over `tokens[..i]` (parser.rs:842). A
leading-comma list, the layout docs/syntax.md:403 describes, therefore
costs O(n) per peek at each comma, and quadratic time over the list. A
10,000-item list at a block's column is roughly 10⁸–10⁹ token visits.

**Fix (S).** Precompute each token's bracket depth once per declaration,
next to `matching`, and look it up. `bracket_depth(start, i)` can become a
difference of two lookups too.

### F10. Two small quadratics (low)

- `block` adds each local definition with `defs.insert(0, def)`
  (parser.rs:2212), which is quadratic in a run of consecutive local
  definitions. Push, then reverse.
- `leftmost_child` and `leftmost_child_mut` (sections.rs:104–147) call
  `span()` on both sides at each level, and `span()` walks the whole
  chain. So `widen` and `leads_with_section` over `.f + a1 + … + an` are
  O(n²). Compare `own_span`s, or use the fact that only a flipped `>`
  swaps the sides.

### F11. Tokens before the first declaration are silently ignored (low)

`split_decls` doesn't start a group at a column-0 `:=`. If the file's
first token is one, every token up to the next column-0 token is in no
group. `parse_module_recovering` never parses them, and nothing reports
them. `decl_ranges` documents the gap. A file that is only `:= 1` loads
as an empty, error-free module. This is an error path that swallows its
error.

**Fix (S).** Report "a declaration can't start with `:=`" on those tokens.

### F12. An indented first line fails the whole file (low)

`split_decls` (parser.rs:406–414) fails everything when the first token
isn't in column 0. With F2's recovery in place, this could instead make
the first group a failed one and carry on.

### F13. Desugared names: how they're marked, and shared spans (low; matters for node ids)

`library_var` says a compiler-written name has an empty span, "which is how
the elaborator tells it from one written". But other desugarings give
their names a real span:

- `prefix_op` writes `Std.Bool.not` with the `!`'s span;
- `exists_chain` writes `Std.Exists` and a `Hole` with the `exists`
  keyword's span, once per layer;
- `reverse_calc` writes `Std.Eq.sym` with the relation's span;
- `interpolated_str` writes `Std.Show.toText` with the `${…` span.

Some of these may be deliberate, for error messages. Either way, "written
by the compiler" isn't a property of the node; it's a convention about
spans, kept in some places and not others. Several nodes also share one
span, and some are copied:

- each layer of an `exists` chain repeats the keyword's span;
- `chain`'s `%chainN` name appears three times (the `let` and two uses)
  with the operand's span;
- `reverse_calc` clones every step's expression;
- `Pattern::CtorFields` caches a built `Pattern::Record` in a `OnceLock`,
  which the derived `Clone` copies.

**For docs/proposals/syntax-node-ids.md.** Carrying ids is cheap if they
go only on `Field`, as §4(a) says: `Field` uses 48 of `Expr`'s 88 bytes.
From this crate's side, the pitfalls are:

- *Copies inside the parser.* The clones in `chain` (atoms only) and in
  `reverse_calc` (whole expressions) and the `OnceLock` cache would all
  need fresh ids. A hand-written `Clone` for `NodeId` covers the first
  two. The `OnceLock` builds its record lazily, after parsing, from cloned
  fields, so ids under it are made on first use, in whatever order the
  elaborator asks.
- *Debug and equivalence.* `NodeId`'s `Debug` must print `_`. Better, F5
  replaces the comparison, so ids never reach a string.
- *Nondeterminism.* A process-wide counter numbers nodes in the order
  threads happen to parse. An id must never be hashed, cached, printed in
  a message, or used to order anything (a `BTreeMap` keyed by `NodeId`
  that is then iterated, for example). Otherwise the same file gets
  different results from run to run, which is exactly the problem being
  fixed. A debug assertion can't enforce this; the type should offer only
  `Eq` and `Hash`, not `Ord`.
- *Spans aren't identities.* Because of the shared spans above, any key
  that falls back to spans conflates nodes, for example
  `Std.Exists` layers or a `%chain` name and its uses.

**Recommendation (S).** Replace the empty-span convention with a field
(an `origin` on `Name`, or a `Desugared` wrapper). Then the elaborator
doesn't have to guess, and ids or spans can't be confused with authorship.

### F14. The non-recursive drop depends on a hand-kept list (low)

`has_nested` and `take_children` (ast.rs:504–720) list every variant's
boxed children. A new variant left out of them drops recursively again,
silently. Handler clauses and rows are left out on purpose, with a
reason. The nesting tests cover the common variants, so this is for new
ones.

**Fix (S).** Add one test that builds a 10⁶-deep tree of each boxed
variant and drops it on a small thread. Or generate both functions from
one table, as `keyword_table!` does.

### F15. `parser.rs`'s size and shape (low)

The file has 8,876 lines, of which 3,600 are the inline `mod tests`
(5,253 on). Up from 7,699 at the 1 Nov review.

The code itself, about 5,250 lines, has one layout oracle (`is_stop`,
which every `peek` goes through) with four context sources:

- the block limit and `allow`;
- `calc_depth`;
- `rewrite_rule` and `rewrite_at`;
- `guard_start`.

The rest is ordinary recursive descent.

There is little duplication with `crates/fmt`. The formatter reuses
`negation`, `record_braces` and `decl_ranges`, and checks its edits by
reparsing them, rather than copying grammar. The one copy is bracket
matching (`fmt::layout::matching_paren` against `match_brackets`), which
is harmless.

`parser` calls `docs::bar_links`, and `docs` calls the parser, so the two
form a cycle. It is small, but it means `docs` can't be split out.

**Recommendation (M, mechanical, in order):**

1. Move the tests to `parser/tests.rs`.
2. Move patterns (`pattern`, `ctor_args`, `record_pattern`, the
   `tuple_*` and `list_*` helpers, `alternatives`) to `parser/patterns.rs`.
3. Move layout (`is_stop`, `continues_*`, `bracket_depth`, `block`,
   `statement`) to `parser/layout.rs`.
4. Move the operators (`logic_chain` through `mul_expr`, `chain`) to
   `parser/operators.rs`.

Then compute the doc links in the driver, not in
`parse_module_recovering`.

### F16. Stale comments in the token list (low)

`Tok::KwMatch` says `match e with | p -> …`; `KwReturn` says
`return x -> …`; `KwLet` says `let x = e`; `FatArrow` says
`get () => k -> …`. The syntax has moved on to `=>` and `let x := e`.

### F17. docs/syntax.md against the grammar (low)

I checked the expression table against the precedence functions:

- `->` < `<->` < `||` < `&&` < comparisons and `in` < `|>` < ranges < `++`
  < `+` < `*` < prefix < application < `.`;
- the associativity of each;
- that `>` is a flipped `<`;
- ranges not chaining;
- the universe bound;
- the escapes and the text-block rules.

All of it agrees. Three slips:

- **Layout bullet** (line 11): "a run of them above a declaration is its
  doc" says plain `--`, but since SW-1044 only `--|` lines make a doc, as
  the Doc comments section itself says.
- **Table order.** The table is "loosest-binding first", but `!a` comes
  after `f a b` while binding more loosely than application, and
  `-e`/`(-k)` sit among the expression rows although `(-k)` is a pattern.
- **Numerals and quotes.** The layout section says names may contain `'`,
  but not that a numeral followed by `'` (`1'…`) lexes as a number and
  then a character literal. That reading is also what F1 trips on.

## Checked and sound

- **Byte-offset slicing in the lexer.** Every `text[i..]` is at an ASCII
  byte (`"`, `\`, `$`, `'`, `-`, a letter), or after advancing by
  `len_utf8`. The `i += 2` past a backslash inside the pre-scan's string
  skip can land mid-character, but continuation bytes never equal ASCII,
  and those positions are only compared, never sliced. The exception is
  F1.
- **Escapes.** `\u{…}` takes 1 to 6 hex digits, rejects surrogates and
  values over U+10FFFF, and slices only hex digits. A backslash at the
  end of the file or before a newline is an error, not a panic.
- **Character literals.** Unclosed, multi-character and empty literals are
  errors. Comments inside `${…}` reach the newline check and are errors.
- **Trivia.** The `expect` on a trailing comment's token holds, because
  `fresh_line` turns false only after a token is pushed. The trivia is
  synced at the top of each iteration.
- **The stack limit.** `StackLimit` measures real stack use, the same in
  debug and release, with `Box<Diagnostic>` keeping frames small. Every
  recursive path in the parser goes through `expr`, `append_expr`,
  `pattern` or `unary`'s prefix branch, each of which calls `deeper()`.
  The driver's nesting tests cover parentheses, applications, function
  types, sums, appends, blocks, pattern blocks, list literals, nested
  patterns and a 4 MB text.
- **Chains built in loops.** `f a b`, `+`, `*`, `&&`/`||`, `|>`, `x.f.g`
  and interpolation pieces are built in loops. `Expr::span` and
  `own_span` walk them in loops, and the `Field` case avoids the
  exponential walk.
- **Indexing.** `Parser::prev_span` and every `tokens[pos - 1]` follow a
  `bump`. `rewrite_body`'s `tokens[pos + 1]` is guarded by `peek_at(1)`.
  `spelled`'s `len() - 2` is on a backticked description.
  `decl_ranges`'s subtraction can't underflow.
- **Bracket matching.** `match_brackets` uses one allocation. The lambda
  and pi lookaheads jump across brackets through it, so they run in time
  linear in the parameter run.
- **Declaration splitting.** A declaration keyword at column 0 always
  starts a group, so an unclosed bracket or `@[` doesn't swallow the file.
- **Docs.** `docs.rs`'s link parsing slices at `find` results. `attached`
  and `file_doc` can't underflow. The binary search by member offset is
  over sorted tokens.
- **Universe levels.** The `Type n` bound is checked before the
  conversion to `u32`.
- **Empty input.** An empty file, or one holding only comments, gives an
  empty module with no error and no panic.
- **Shared rules.** The keyword table and the negation rules are single
  sources shared with the formatter and the highlighters, with tests.

Not checked: offsets past 4 GiB (`as u32` casts would wrap; not realistic),
`BigUint` parsing time on numerals with millions of digits, and the
elaborator's own handling of deep syntax.

## The 1 November review's findings in this scope

The whole-codebase review (docs/research/rust-codebase-review.md) has one
finding for this crate: `syntax/parser.rs`'s size (7,699 lines; §4.4,
and §6 item 6, "improve review locality"). The architecture review's item 12
lists the same split.

**Still open, and larger:** the file has 8,876 lines now (F15). Its other
note, the `parser`/`ast`/`docs` cycle (architecture-review.md:146), is
still there.

## Tickets to file

Grouped into lanes, each 30–90 min.

1. **Lexer: `"""` interpolation panic, byte-order mark, invisible
   characters, stale docs** (F1, F6, F16). Opus, since the lexer is syntax
   core (D2506). About 60 min. Tests: lexer unit tests for both F1
   repros, a byte-order mark, a no-break space and CR-only line endings.
2. **Lexical error recovery and namespace-line robustness** (F2, F12).
   Opus, about 90 min. Tests: a recovering parse of a file with a tab, an
   unclosed `"` and a `∀` in separate declarations keeps the others;
   `parse_namespace_line` succeeds on a file whose body doesn't lex.
3. **Recursion after parsing: chains, `exists`, patterns** (F3, F4, F14).
   Sonnet, about 60 min. Rewrite `chain`, `exists_chain`, `has_absurd`
   and `first_bound` as loops; give `Pattern` a non-recursive `Drop`; add
   the nesting tests for long chains, list patterns and tuple patterns,
   and a drop test per boxed variant.
4. **`equivalence` without `Debug`** (F5). Sonnet, about 60 min. An
   iterative tree equality ignoring spans; the formatter switched over; a
   test with a 5,000-line block and a 50,000-term sum.
5. **Fuzz test rework** (F7). Sonnet, about 90 min. The new generators,
   span invariants, more entry points, and running each case on a thread.
   It should find F1 before lane 1 lands, which is worth checking.
6. **Quadratic spots** (F9, F10). DeepSeek, about 30 min: the per-token
   depth table, push and reverse, own-span comparison. One timing test
   with a 20,000-item leading-comma list.
7. **Small correctness and docs fixes** (F11, F13's origin marker as a
   separate step, F17). DeepSeek for F11 and F17, about 30 min. F13 needs
   the elaborator's side, so Sonnet, with lane 3 or after it.
8. **Split `parser.rs`** (F15). DeepSeek, mechanical, about 45 min for
   steps 1 and 2 (tests, patterns), with no behaviour change. Run it after
   lanes 3 and 6, which touch the same functions.
9. **Recovery inside a declaration** (F8). Opus, a design note first
   (docs/proposals/), about 60 min for the note. D2692 asks whether to
   start it.

## Questions for Matt

- **D2690.** Should one lexical error, such as a stray tab, an unclosed
  `"` or a `∀`, cost only its own declaration, and no longer empty the
  whole file and drop it from its project? **Rec: yes** (lane 2). It is
  what the editor shows most often while someone types.
- **D2691.** Should a byte-order mark at the start of a file be skipped
  silently, as Rust and Go do, rather than be an error? **Rec: yes.**
  Rejecting it gains nothing, and the current message shows an invisible
  character.
- **D2692.** Should the parser recover inside a declaration, keeping a
  definition's signature when its body fails and the other arms when one
  arm fails, so a half-typed theorem keeps its goals? **Rec: yes, design
  note first** (lane 9), after D2690's lane.
