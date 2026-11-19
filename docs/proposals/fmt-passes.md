# The Rust formatter as tidy passes, then a white-space printer

SW-3492. A plan, written 16 Nov 2026, for D3624: reshape `crates/fmt` into
the architecture D3623 chose for the Stitchwort formatter (direction C of
[after-the-toy-proof.md](after-the-toy-proof.md) §4.3), with no proofs.

## In plain words

**The problem.** The formatter changes more than white space: it adds `∀`,
drops brackets and commas, merges parameters and moves comments. It does
these in three different places: on the text before parsing, inside the
layout rules, and inside the layout engine. When the layout depends on
something the printer is about to change, the second run sees a different
program and lays it out differently. That is the bug family the overnight
fuzzers found four times (SW-3481, SW-3482, SW-3485, SW-3487), each fixed
by one more rule remembering to ask `comment_ends_at_closers`.

**The change.** Every one of those changes becomes a *pass* that runs
before printing, on the whole file, and finishes in one go. Comment
placement becomes one rule for where a comment *belongs*, applied whenever
the formatter reads a file, so the printer and its check both see the same
answer. The printer is then left choosing only spaces and line breaks, and
the check after it can be exact: the same tokens, the same comments on the
same tokens, the same tree. The "left as written" fallback goes.

**What it should do.** End the "formatting twice differs" family by
construction rather than by fuzzing, keep the output byte-identical on all
59 golden pairs except where listed in §5.1 (estimated: one line in the
repository changes, `tools/toyfmt/src/Toy/Fmt/Tests/Probes.sw:109`), and
give the self-hosted formatter the same shape to copy. Six lanes, about
4 h of agent time in all (estimated, §6).

## 1. Every change beyond white space

Line numbers are at `f968b784e`. The note's §4.1 table is complete for the
big rewrites. Rows marked **new** are ones it missed or placed elsewhere.

| # | What changes | Where | How it's done today |
|---|---|---|---|
| C1 | `∀` added after a theorem's name when it has explicit parameters (D3472) | `lib.rs:127-179`, called at `printer/mod.rs:162-163` (**new**: the note says `printer/mod.rs:10`, which is only the doc comment) | text, by a token scan, before parsing |
| C2 | Redundant round brackets dropped after an ability row and around a header binder's whole type (D2307) | `printer/parens.rs:134-237` | text, each candidate checked by re-parsing the declaration |
| C3 | Adjacent parameters of one type merged, `(a: Nat) (b: Nat)` to `(a b: Nat)` (D3565) | `printer/merge.rs:132-192` | text, checked by `merge::check` (`merge.rs:223`) |
| C4 | A comma before a closing bracket dropped (D1012) | `printer/rules.rs:1093-1108`, its comments printed at `:1163-1165` (`leaf_trivia_only`, `:370`) | inside the comma-bracket rule |
| C5 | A comma that starts a line moves to the end of the line above; comments on either side of it become own-line comments of the next item | `printer/rules.rs:334-367` (`comma_first_comments`, `comma_end`), `:1157-1161`, `:1882-1886` | inside the rules. Moving the comma is white space (token order is unchanged); moving its comments is not |
| C6 | A trailing comment written before closing brackets or commas is printed after them | **two places**: the rules ask `comment_at_closers` (`rules.rs:459-480`, used at `:1082`, `:1355`, `:1383`, `:1438`, `:1605`, and `holds_comment_before_code`, `:439-453`); the engine writes closers and commas before a waiting comment (`engine.rs:449-470`, S39) and measures the same way (`engine.rs:592-604`) | rules and engine |
| C7 | **new:** a record update's base keeps its trailing comment after the `\|`, `{ r \| -- c` (S31) | `rules.rs:1071-1092` (`defer_trailing`, `:61`, `:301`); its check counterpart `printer/mod.rs:318-325` | inside the rules: a comment moves across a token that isn't a closer |
| C8 | **new:** comments lose their trailing spaces | `rules.rs:272`, `:286`, `:306`, `:352`; `printer/mod.rs:208`, `:263` | a comment's text changes |
| C9 | A `"""` text block's lines move with their line | `rules.rs:313-324`, `engine.rs:411-416`, `:512-534`, `shift_lines` `:712` | the token's text changes, its value doesn't |
| F1 | A declaration whose output fails the checks is left as written | `printer/mod.rs:226-254` (`same_decl`, `:371`); `REFUSE_FOR_TEST`, `:35` | fallback |
| F2 | **new:** a declaration that is an `Error` node, or starts with `:=`, is printed as written without trying | `printer/mod.rs:217-218` | fallback |
| F3 | **new:** a declaration that didn't lex is copied raw (only a refused file has one, so unreachable) | `printer/mod.rs:198-201` | fallback |
| F4 | A node with no rule, or a shape a rule doesn't expect, is printed as written (`Doc::Verbatim`) | `rules.rs:485-497`, `:533`; **new**, the shape guards: `:589` (decl), `:932` (data type), `:1151` (empty comma-bracket item), `:1657`, `:1660` (`if`), `:1855` (`rewrite`) | fallback |
| K1 | The token check ignores every comma and round bracket | `check.rs:203-211` | check, loose |
| K2 | The comment check lets a trailing comment slide left over commas and closers, counts tokens without commas, and re-homes the comments of line-first commas and record-update bars | `printer/mod.rs:294-341` (`comment_anchors`) | check, loose |
| K3 | **new:** a failed parameter merge makes the whole file `Error::Internal` (`printer/mod.rs:100`), but a failed bracket drop is silently skipped, judged by the *merge's* check (`printer/mod.rs:166-170`) | `printer/mod.rs` | inconsistent checks |
| K4 | Multi-line tokens pass the text comparison if both contain a line break (`check.rs:216`); the `Tok` comparison still compares the text block's value | `check.rs:213-223` | check, intentionally loose |

Not token changes, and staying in the printer: blank lines capped at one
(`printer/mod.rs:185-193`, `rules.rs:254-297`), spaces between tokens
(`spacing.rs`, including copying the source's gap where it changes
meaning), trailing spaces removed at a line end (`engine.rs:502`).

**A latent bug found while reading (C4).** A dropped final comma's own-line
comments are printed by the generic rule (`leaf_trivia_only` →
`leading`, `rules.rs:281-291`), but on the second run the parser attaches
them to the closing bracket, which prints them by the S40 closer rule
(`rules.rs:261-279`) at a different indentation. Not confirmed with a
test (paper lane); the comma pass below removes it by construction. Worth
a golden in lane L3.

## 2. The passes

Two kinds, because the current syntax tree (§3.2) can represent one and
not the other:

- **The reading rule (N):** where each comment belongs. It is a function
  on the tree's trivia, applied every time the formatter builds a tree,
  input or output. It has to be: plain text can't express its result (a
  trailing comment on `a` in `a) -- c`; the lexer attaches it to `)`).
- **Tree passes (P1-P4):** each reads the tree and returns edits to the
  token sequence; the runner applies them to the text and re-parses. The
  re-parse is the tree constructor, so every intermediate is a real
  program and N is re-applied for free.

### N. Where a comment belongs (C5, C6, C7, C8)

*Does:* rewrites each token's trivia:

1. A trailing comment on a comma, a closing bracket or a record update's
   `|` moves to the nearest token before it that is none of those. (The
   leftward walk is what `comment_anchors` already does for the check,
   `printer/mod.rs:321-333`, and what `comment_at_closers` does for the
   layout.)
2. A comma's own-line comments, and the trailing comment of a comma that
   starts its line, become own-line comments of the token after the comma,
   with its blank lines (today's `comma_first_comments`).
3. Comment text loses trailing spaces.

*Tidy when:* no comma, closer or record-update bar has a trailing comment;
no comma has any comment; no comment text ends in a space. N on a tidy
tree changes nothing (each step only moves comments off tokens the next
step never puts them on).

*The printer may assume:* the three facts above. So "this element ends
its line with a comment" is one lookup on the element's last code token,
the same however the source was written; commas print as bare text; the
record-update rule prints the base's comment after `|` without searching.

*Why it is right:* the printer puts a trailing comment at the end of the
line its token ends on, after any closers and commas that join that line
(the engine's S39 rule, which stays: it is now white space, because the
anchor no longer depends on which side of the closers the comment sits).
Reading the output back, the lexer puts the comment on the last closer,
and N moves it back. So `N(parse(print t)) = t` on comments.

### P1. Theorem `∀` (C1)

*Does:* inserts `∀` after the name of a `Theorem` node with an explicit
`(` parameter and a result type and no `∀` yet. As now, the edit goes
before the first parameter when it shares the name's line, else at the end
of the name's line (a text-placement choice only).

*Tidy when:* every such theorem has its `∀`.

*Printer may assume:* nothing new (the header rule already prints `∀`
as a token).

The rewrite moves it from a token scan (`lib.rs:127`) to the `Theorem`
node's children, which also covers theorems in blocks without the depth
counting.

### P2. Trailing comma (C4)

*Does:* deletes a comma directly before the closer of a comma bracket
(`List`, `Tuple`, `Record`, `Fields`, the three pattern kinds,
`Attributes`, an import list). After N it has no comments to re-home.

*Tidy when:* no comma bracket ends with a comma.

*Printer may assume:* the comma-bracket rule's items alternate item,
comma, item, and end with an item: the `dropped` branch
(`rules.rs:1103-1108`, `:1163-1165`) goes.

*Check for the lane:* `api.rs:126` shows `[(x),]` and `[(x)]` read the same;
confirm what `(e,)` parses to (syntax.md:1625 says there is no one-element
tuple). If it is a `Tuple` node that becomes a `Paren` node, the tree kind
changes and the meaning doesn't, which is fine, but P3 must run after P2
(§3).

### P3. Redundant brackets (C2)

*Does:* as `drop_parens` now, finding every droppable pair, nested ones
included, in one run (SW-3482's fix, `parens.rs:168-221`), and returning
the pairs as deletions instead of text.

*Tidy when:* no pair after a row or around a binder's whole type would
leave the declaration's tree unchanged if dropped, among pairs with no
comment on their own tokens. P3 strips brackets around a binder's type
only along a header's type, so a lambda in a value such as
`(x: (A)) (y: A) => …` is neither stripped nor merged.

*Printer may assume:* nothing new; it is needed for idempotence of the
whole formatter, since the layout always joins the type to the row.

One output change (§5.1): a comment written after the `)` of such a pair
moves inside it under N, so the pair, today kept, is dropped.

### P4. Parameter groups (C3)

*Does:* as `merge::merge` now, as edits.

*Tidy when:* no two adjacent parameters of one bracket and the same type
text, without comments, defaults or `auto`, whose type mentions none of
the run's names.

*Printer may assume:* nothing new.

### Not passes, and why

- **C9, text blocks.** The new indentation depends on the column the
  printer chooses, so no pass can know it. It is white space by
  definition: the lexer already de-indents a `"""` literal to its value
  (`lexer.rs:1108-1111`), and the token check compares values. It stays
  in the printer and K4 stays loose for multi-line tokens only.
- **Moving a line-first comma to the line above (C5's comma).** Token
  order doesn't change, so it is white space; only its comments needed N.
- **The engine's S39** (closers and commas written before a waiting
  comment). White space given N.

## 3. Order, interactions, and the tree

### 3.1 Order

```
parse+N  →  P1 ∀  →  P2 trailing comma  →  P3 brackets  →  P4 groups  →  print  →  check
```

Each arrow from P1 on is "apply edits, re-parse, apply N", skipped when
the pass made no edits (most files).

| Pass | Can it untidy … | So |
|---|---|---|
| N | P3: a comment on a pair's `)` moves inside, making the pair droppable | N first (it is part of every parse anyway) |
| P2 | P3: dropping the comma of `((Nat, Nat),)` can leave a droppable outer pair | P2 before P3 |
| P3 | P4: dropping the brackets of `(a: (Nat)) (b: Nat)` makes the types equal | P3 before P4 |
| P4 | nothing: a merged group keeps the first type's text, already tidy for P3, and no comma or `∀` | last |
| P1 | nothing: no other pass looks at `∀` or changes whether a parameter is explicit | first or anywhere |
| P2, P3, P4 | N: no, N is re-applied at every re-parse | |

No pass undoes another's work, so one run of the sequence is tidy for all
of them: each pass's condition is preserved by the passes after it (the
table's "nothing" rows), which is theorem 3 of §4.3 in the Stitchwort
version.

### 3.2 The tree

The current lossless tree is enough for Rust; no new typed tree is needed.
It isn't rowan: `SyntaxFile` (`crates/syntax/src/tree.rs:434`) stores the
tokens, one `Trivia` per token, and each declaration's nodes flat in
preorder over token ranges, with 94 untyped kinds. It is immutable and its
tokens point into the source text, which the rules also read for white
space (`spacing.rs`'s copied gaps, `rules.rs:216` line indentation).

So:

- **N** lives in `crates/fmt` as a function from the trivia array to a new
  one. The rules read trivia from a field holding N's result instead of
  `self.file.trivia()` (8 call sites in `rules.rs`). No change to
  `crates/syntax`. (The alternative, a `SyntaxFile::with_trivia` in the
  syntax crate, would let other tools see the same anchors; not needed
  now.)
- **P1-P4** emit edits (insert a token's text at a byte, delete a token),
  which the runner applies and re-parses. That keeps the passes' outputs
  honest programs, reuses the parser as the only tree constructor, and
  changes nothing in `crates/syntax`.

The self-hosted version will want a typed tree for the proofs (risk (i)
in the note's §4.3); the Rust version doesn't, because nothing is proved
by cases over it. What carries over is the pass list, their tidy
conditions, the order and N's rule.

## 4. The printer afterwards

### 4.1 What goes from `rules.rs` and `engine.rs`

| Goes | Lines |
|---|---|
| `comma_first_comments`, `comma_end`, `leaf_trivia_only`, `comma_first_on_line` | `rules.rs:334-374`, `:1882-1886` |
| the trailing-comma branch of the comma bracket | `rules.rs:1103-1108`, `:1163-1165` |
| `comment_at_closers`'s tolerance: it becomes "the trailing comment of the element's last code token", one definition with no record of which side it was written | `rules.rs:455-480` |
| `holds_comment_before_code` and `holds_trailing_comment` simplify (a closer never holds one) | `rules.rs:427-453` |
| the search in the record-update rule; `defer_trailing` stays, as a placement | `rules.rs:1077-1091` |
| `as_written` and `Doc::Verbatim`, and its measuring branch | `rules.rs:485-497`, `engine.rs:89-92`, `:682-684` |
| comment trimming at each print site | `rules.rs:272`, `:286`, `:306`, `:352` |

What stays: every layout rule (the 73 functions), the engine, the S39
closer rule and S40 comment breaks (white space under N), `TextBlock`,
blank lines, spacing. The six unexpected-shape guards (F4) become an
internal error for the file (a flag the rules set, read by the printer),
not a verbatim copy. An assertion goes into the engine: a waiting
trailing comment is never written at a line start (`engine.rs:487-489`
does that today; after N nothing should reach it).

### 4.2 The checks

After the passes, the check compares the tidied input with the output read
back through `parse+N`:

- **tokens: exact.** `check.rs:203-211`'s strip goes; a multi-line token
  may still differ in text if its value is equal (C9).
- **comments: exact**, as (text, own-line or trailing, token index), with
  blank-line counts left out. `comment_anchors` (`printer/mod.rs:294-341`)
  becomes "both sides' trivia after N".
- **tree: exact**, the parse shape, with no merge-splitting (the tidied
  input already has the merged groups).

### 4.3 The fallback

The per-declaration fallback (F1) goes, with `REFUSE_FOR_TEST`,
`VerbatimDecl`, `Stats::verbatim_decls`, `Formatted::verbatim_at`,
`golden.rs`'s `LEFT_AS_WRITTEN`, and the CLI's report of them
(`crates/cli/src/main.rs:4291`, `:4387-4420`, `:5175-5203`). Over std,
`aoc/` and `games` it is used by 0 of 15,829 declarations [measured,
self-hosted-fmt.md §1], so the output doesn't change. F2 and F3 go: F3 is
unreachable, and F2's `Error` node can't occur in a file the formatter
accepts; a `:=`-first declaration needs a look in lane L5 (what parses
that way, and whether its rule handles it).

The whole-file check stays as an assertion: a failure is
`Error::Internal` and the file is left unchanged, as now (`lib.rs:25-27`).
See decision D-A in §7.

## 5. Testing

### 5.1 Golden files

All 59 pairs (`crates/fmt/tests/it/golden`) should stay byte-identical,
since N reproduces what `comment_at_closers` and the engine already do at
every decision point. Expected differences, each from a source spelling no
golden or repository file uses today except the one named:

1. A trailing comment written after a closer that starts its own line,
   `[\n  a\n] -- c`, prints on the last item's line, `a -- c` then `]`.
   One line in the repository: `tools/toyfmt/src/Toy/Fmt/Tests/Probes.sw:109`
   (`) -- after the header`). Searched with `grep -E '^\s*[])}]+[]),}]*\s+--'`
   over the formatted `.sw` files.
2. A pair after a row whose `)` carries a trailing comment is now dropped
   (P3 after N).
3. A dropped final comma's own-line comments print by the S40 closer rule
   (the latent bug in §1).

Each lane blesses only these; any other golden diff is a bug in the lane.
New goldens: one per item above, the four bug tickets' inputs (already
goldens: `application-argument-comment-before-closer` and the others
added by SW-3481/3482/3485/3487), and a "comma comments" set.

### 5.2 Fuzz properties per pass

In `crates/fmt/tests/it/fuzz.rs`, behind `FUZZ_PASSES=1` so the default
run is unchanged, for every case that parses:

- **finishes:** `pass(pass(t)) = pass(t)`, checked as "the second run
  makes no edits";
- **keeps the meaning:** the parse shape (`equivalence::shape`) of the
  pass's output equals the input's (P4 compares after splitting groups,
  as `merge::check` does now). This is the parse-level hash. Declaration
  content hashes need elaboration, which mutated programs mostly don't
  survive; they are covered by Overmind's rolling repository check, where
  every formatted file elaborates;
- **keeps earlier passes tidy:** after the whole sequence, each pass on
  its own makes no edits (§3.1's table, checked);
- **N is idempotent.**

### 5.3 The printer property

For every formatted case: `parse+N(print(t)) = t`, comparing tokens,
comments as in §4.2 and node kinds with their token ranges, not only
the shape. This is the exact form of the toy's theorem 4, and it is what
SW-3481, SW-3485 and SW-3487 broke. Idempotence then follows (the
formatter on a tidy tree prints the same tree), and the fuzzer keeps
checking it directly.

## 6. Lanes, in order

Each keeps `main` working and the goldens passing. Estimates are agent
time, from similar fmt lanes (SW-3481-3487 took 30-45 min each on
DeepSeek). Tests are named ones in the fmt crate plus short fuzz runs;
never `repo.rs`'s whole-repository test, which is the verifier's and
Overmind's.

| Lane | Model | Est. | What | Tests it runs |
|---|---|---|---|---|
| L1 N, the reading rule | Opus | 60 min | `fmt::tidy` module: N over trivia; `Rules` reads N's trivia; `comment_at_closers` becomes one lookup; `comma_first_comments`, `comma_end`, `comma_first_on_line` and the comment trimming go; `comment_anchors` becomes "trivia after N, exact" (commas still skipped until L2) | `golden_files_format_as_expected_and_idempotently`; `printer::tests::comments_*`, `a_comment_before_a_closing_bracket_moves_to_the_line_end_without_changing_the_layout`; N unit tests; `task fuzz:fmt CASES=20000 COMMENTS=0.3` on two seeds, including 0x805 |
| L2 runner, P1, P2 | Sonnet | 45 min | `Pass` trait and runner (edits, re-parse, skip when none); `∀` moved to a pass on `Theorem` nodes (`lib.rs:127` goes); trailing comma as a pass, the comma bracket's dropped branch goes; the check stops skipping commas | `a_theorem_with_explicit_parameters_gets_forall`, `a_trailing_comma_does_not_change_the_tree`, `the_theorem_forall_is_added`, `an_attribute_list_that_fits_drops_its_trailing_comma`, the golden test; the §1 latent-bug golden, failing first |
| L3 P3, P4 | DeepSeek | 40 min | `drop_parens` and `merge` return edits through the runner, in §3.1's order; the `merge::check` gating and the K3 inconsistency go; the check stops skipping round brackets | `parens::tests::*`, `merge::tests::*`, the golden test; `task fuzz:fmt SEED=0x60c CASES=30000` |
| L4 exact check, no fallback | Sonnet | 45 min | §4.2's exact checks; F1-F4 removed (shape guards become an internal error); `Doc::Verbatim` goes; stats, CLI report and `LEFT_AS_WRITTEN` go; the engine assertion | the golden test, `api.rs`'s tests by name, `printer::tests` by name; builds `stitchwort` once |
| L5 fuzz properties | DeepSeek | 35 min | §5.2 and §5.3 in `fuzz.rs` behind `FUZZ_PASSES=1` | the new properties at `CASES=20000`, plain and `COMMENTS=0.3` |
| L6 docs | DeepSeek | 15 min | `formatter-architecture.md` and `formatter-style.md` describe passes then printer; module docs in `printer/mod.rs` and `lib.rs` | none (prose) |

L1 is the one that ends the bug family; it can merge alone. L2 needs L1
(commas carry no comments). L3 needs L2's runner. L4 needs L1-L3 (exact
checks are only true once every change is a pass). L5 can start after L2
and grow as passes land. L6 last, or with L4. In all about 4 h of lane
time; L1-L3 can't overlap (they edit the same files), L5 can run beside
L3-L4.

After L4, Overmind should run the long comment-mode seeds that found the
four bugs (0x500, 0x502, 0x504, 0x60c, 0x805, 0x80a, 0x80e, 0x80f, 0x811)
at their full counts, and one `stitchwort fmt --check` timing over std to
see the cost of the extra re-parses (expected small: a pass re-parses only
a file it edited).

## 7. Risks and open questions

- **Re-parse cost.** Up to three extra parses of a file that a pass edits,
  plus P3's per-candidate parses (as now). Not measured; Overmind's
  timing after L4 settles it. If it matters, P1 and P2 can share one
  re-parse, since neither can affect the other.
- **The leftward rule changes one visible case** (§5.1, item 1): a comment
  after a closer on its own line moves up to the last item's line. The
  alternative (anchor rightward, on the last closer) changes the far
  commoner `a -- c` then `]` instead. The orchestrator's call, recorded on
  the ticket, not Matt's: it is a wording-sized style change with one
  instance.
- **F4's shape guards might be reachable** in a file the formatter accepts
  today. If so, the file would become `Error::Internal` where today one
  node is copied. L4 counts them first (they are not in
  `stitchwort dev fmt-tree`'s unruled counts, which cover only `Error`
  nodes, `rules.rs:27-29`), and adds a rule for
  any that occurs.
- **The rules still read white space from the source** (copied gaps,
  line indentation for text blocks, `line_start`). Harmless in Rust; for
  the Stitchwort proof it means the printer's input is the tree *with*
  those facts, and the theorem is stated up to them. A note for the
  self-hosted plan, not a blocker.
- **Byte comparability with the self-hosted formatter.** Its port should
  start from the reshaped Rust formatter (after L4), so it ports passes
  and a printer, not the rules' comment tolerance.

### Decisions for Matt

**D-A: keep a run-time check in the Rust formatter?** [rec: yes]

*The problem.* D3623 drops the check in the Stitchwort formatter because
proofs replace it. The Rust formatter will have no proofs.

*The change.* Keep one whole-file check (exact tokens, comments and tree
after reading the output back): if it fails, the file is left unchanged
with a "formatter bug" error, as today. Drop only the per-declaration
"left as written" fallback, as D3623 says.

*What it should do.* A formatter bug can never change a program's meaning
on disk, and the fuzzers keep their oracle. Cost: one extra parse per
formatted file, as now (unchanged from today). The alternative, no check,
saves that parse and makes a bug silently write a different program.
