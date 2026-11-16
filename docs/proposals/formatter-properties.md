# Formatter properties: which are worth proving

Fable paper lane, SW-3626, 16 November 2026 (D3662). No builds or tests
were run and no code was changed. Read at `ba1168c51`: the board's
formatter tickets, the 27 fuzz minimal inputs (the session's scratchpad,
`fmtbugs/` and `fmtbugs/round2/`), `crates/fmt/src/check.rs` and
`same_program.rs`, [toy-plus-plus.md](toy-plus-plus.md) and T0's
[SKETCH-PLUS.md](../../tools/toyfmt/plus/SKETCH-PLUS.md) with its
`src/Proofs.sw`, `Meaning.sw`, `Format.sw` and `Passes.sw`.

How claims are marked: **[checked]** read at the place given;
**[inferred]** my reasoning, nothing run; **[estimated]** my estimate,
from T0's lemma counts and the measured rate of about 80 lemmas a lane in
25 to 50 minutes (toy-plus-plus.md §5).

## In plain words

**The problem.** Toy++ plans three theorems: the output parses, it has
the same `meaning`, and formatting twice changes nothing. All three
compare two parse trees. So anything `parse` itself loses is lost on both
sides and never seen, and nothing says the formatter does anything at
all. The real formatter's worst bug (SW-3606, a comment silently lost)
was the same mistake in a run-time check: the check reused the code it
was checking.

**The change.** Add four small statements to the three: every comment is
kept, stated between the two *texts* through the lexer alone; rule N
moves a comment only past closers and commas; the output depends only on
the tree, not on how the source was laid out; and a file of silly
formatters, each shown to break a named theorem. Leave width, style and
locality to goldens and the fuzzers.

**What it should do.** Every failure class seen so far in the real
formatter is then covered by a theorem, except style and resource limits,
which stay tests. The cost is about 40 to 60 lemmas, ten examples and 45 minutes
of agent time on Toy++'s 5 h 15 min [estimated, §4].

## 1. Failure classes seen so far

From the real formatter's tickets and the fuzz minimals. "Caught" means a
run-time check refused the output and the file was left as written.

| # | Class | Tickets | Caught at run time? |
|---|---|---|---|
| F1 | **Output doesn't parse.** A comment forces a line break where layout matters (`→`, `else`, a match bar, `;`, a calc step at or left of the block's column) | SW-3570, 3571, 3572, 3573, 3574, 3575, 3587, 3605 (five families) | yes |
| F2 | **Output parses to a different program.** Re-indenting or joining lines regroups match arms, turns a block type into an application, a row into a record | SW-3582 (three cases), SW-1355, SW-3594 | yes |
| F3 | **A comment silently lost.** Rule N overwrote a token's comment | SW-3606 | **no**: exit 0, comment gone |
| F4 | **A comment moved** to another token, or two ran together on a line | SW-3580, SW-3196 | yes |
| F5 | **A check that can't fail.** The comments check ran the placement code on both sides; the tree check compared the output with the already-tidied text; `fmt_hashes` compared a formatted corpus with itself | SW-3606, SW-3610, SW-3026 | n/a: this is why F3 got through |
| F6 | **Not idempotent.** A second run joins or splits a line the first left | SW-1789, SW-2466, SW-3203 | by the fuzzer only |
| F7 | **Layout kept as written.** Two layouts of one program both count as formatted | SW-3033 (157 of 1,692 de-formatted files didn't format back), SW-2691 | no |
| F8 | **Refuses, or leaves as written, a file that parses**, sometimes without saying | SW-3196, SW-3230, and every F1 and F2 case | n/a |
| F9 | **Tokens glued or brackets dropped where they matter.** `- -x` printed as `--x`; a tidy pass dropping a pair that groups | `neg.sw`, `check.rs`'s tests, SW-3610's test, SW-1212 | yes |
| F10 | **Poor layout that is still correct.** Width counted in bytes, long lines left, an orphan parameter, `, ]`, a lone `:` | SW-3163, 3187, 3193, 3195, 3578, 3192, 3164, 3298, 3560 | no (goldens, the dry run) |
| F11 | **Resources.** Stack overflow on deep input; most of the time spent in the check itself | SW-1968, SW-1956, SW-3147 | no |
| F12 | **The driver.** `fmt DIR` rewrote folders it should skip; "no such file" | SW-3204, SW-1951, SW-2618 | no |

Two lessons the classes share:

- F1, F2, F8 and F9 are one thing in a proved formatter: `printParses`
  (the printed tree parses back to itself). 18 of the 27 fuzz minimals are
  of this kind, and most involve a comment [checked: the minimals].
- F3 and F5 are one thing too: **a statement that goes through the code
  it is about**. The proof-side form is a theorem stated through `parse`
  when `parse` is what might be wrong.

## 2. Candidate properties

The three planned theorems first, then the candidates. Statements are
sketches against T0's names (`tools/toyfmt/plus/src/`).

**P1. Formats whatever parses, and the output parses** (planned:
`formatAnswers`, `formatRoundTrip`, resting on `printParses`).

```
theorem formatAnswers ∀ (source: Text) (width: Nat) (tree: SourceFile) (parsed: parse source = Ok tree):
    format source width = Formatted (tree.tidy.print width)
```

**P2. Same meaning** (planned: `formatKeepsMeaning`). `meaning` keeps
every comment on its node and every `blankBefore` flag [checked:
`Meaning.sw`], so after parsing it already covers comment attachment and
blank lines.

**P3. Idempotence** (planned: `formatIdempotent`). "The output is a fixed
point of parse-then-print" is the same statement: `formatIdempotent` is
proved from `formatRoundTrip` and `tidyIdempotent` [checked:
`Proofs.sw`]. Not a separate candidate.

**P4. Every comment kept, text and order, between the two texts.**

```
theorem formatKeepsComments ∀ (source output: Text) (width: Nat) (before after: Lexed)
    (formats: format source width = Formatted output)
    (lexedBefore: lex source = Ok before) (lexedAfter: lex output = Ok after):
    commentsOf after.tokens after.endTrivia = commentsOf before.tokens before.endTrivia
```

It mentions `lex` and `commentsOf` (four lines) and nothing else. `lex`
is itself pinned by `lexCovers` (the lexemes joined are the source), so
no comment can hide there. Proof: three pieces, used on both sides.
(a) `settledKeepsComments`, already stated by T0. (b) The parser's half:
`file.comments = commentsOf` of the settled tokens, one more conjunct of
the walk. (c) `meaning` equal gives `comments` equal
(`plainKeepsComments`: `plain` drops a pair only when it holds no
comment, and splits a group with the comments on its last name
[checked]). Then output's comments = (a) = (b) the output tree's = (c)
the input tree's = (b) = (a) the source's [inferred].

**P5. A comment stays where it was: rule N's reach.** After parsing,
attachment is P2's. The one mover the three theorems can't see is
`settle`, inside `parse`: a `settle` that sent every comment to the top
of the file would keep P1 to P4.

```
--| Rule N moves a comment only back past closers and commas, or forward
--| from a comma to the next token: the tokens it crossed hold no code.
theorem settledNear ∀ (lexed: Lexed) (index: Nat) (comment: Comment)
    (held: holdsAt lexed.settled.tokens index comment):
    ∃ (from: Nat) => holdsAt lexed.tokens from comment ∧ onlyClosersBetween lexed.tokens from index
```

With `settledOffsets` (T0: the tokens themselves don't move) this says
all of rule N.

**P6. Blank lines and doc comments.** Blank lines: `blankBefore` is in
the tree and in `meaning`, so P2 covers them after parsing; a text-level
form ("a blank line before statement k in the output iff one in the
source") would guard the parser's reading of them. Sprig has no doc
comments [checked: `Lex.sw` has one comment kind]; in Stitchwort a `--|`
comment must stay with its declaration, which is P2 once doc comments
are in the tree.

**P7. Layout-independence, weak form: the output depends only on the
tree.**

```
theorem formatSameTree ∀ (first second: Text) (width: Nat) (tree: SourceFile)
    (parsesFirst: parse first = Ok tree) (parsesSecond: parse second = Ok tree):
    format first width = format second width
```

One line from `formatAnswers`. It is the only candidate that says the
formatter *does* something: the identity formatter fails it on any two
layouts of one tree.

**P8. Layout-independence, strong form: a normal form for `meaning`.**
`first.meaning = second.meaning → format first = format second`. T0
found it false as designed (finding 4: P1 leaves `takes` as written on a
function with no parameters; P3 keeps one comment-free pair) and
recommended testing it with the disturber.

**P9. Code tokens kept, up to the tidy changes, between the two texts.**
The text-level twin of P2, as P4 is for comments: erase the tokens the
passes may add or remove (`(`, `)`, `,`, `takes`, a merged group's
repeated `:` and type) and the two token lists are equal.

```
theorem formatKeepsTokens … : essential after.tokens = essential before.tokens
```

Its worth is independence from `meaning`, the one trusted definition
(about 60 lines); `essential` is about 5. It is `check::same_tokens`
made a theorem.

**P10. Width.** "No line is wider than `width` unless it has no place to
break", and "what fits on one line is put on one line" (D3560b). Both
need a statement of what the engine's breaks are; the toy's engine
theory proves that the output reads back, and no theorem bounds a
line's width [checked: the theorem names in `Doc/*.sw`].

**P11. Termination and totality.** `format: Text → Nat → FormatResult`
has no `Partial` and no `Fail` in its type, so the checker has already
proved it [checked: `Format.sw`]. Nothing to state. Stack depth and time
in native code are outside any theorem.

**P12. Tidy output.** No trailing spaces, no tabs, one final newline, no
two blank lines running, indentation in steps of two. Facts about the
engine's output alone.

**P13. Locality.** Editing one declaration leaves the others' output
alone: at tree level, a file's print is its declarations' prints joined.
At text level it also needs the parser to read declarations
independently.

**P14. Input that doesn't parse.** `parse source = Err message →
format source width = ParseError message`: by computing. "The driver
then writes nothing" is a statement about `Toy.Fmt.run` under
`Files.simulate`.

**P15 (added). The silly formatters, as a checked file.** Not a theorem
about `format`: a file `Degenerate.sw` defining each formatter of §3 and,
for each, a `byComputing` example that breaks one named theorem's
statement; and for `meaning`, examples that two files differing in a
comment, a blank line, an operator or the order of two declarations have
different meanings. It is F5's lesson applied to the contract: each
statement is shown able to fail.

| | Property | Failure classes ruled out | Silly formatters ruled out | Value | Toy++ cost [estimated] | Real formatter later? |
|---|---|---|---|---|---|---|
| P1 | formats what parses; output parses | F1, F8, F9 (glue) | refuse everything; emit rubbish | **high**: 18 of 27 fuzz minimals | planned (T1 to T3) | yes; it is what removes the re-parse |
| P2 | same meaning | F2, F4 after parsing, F9 (brackets) | reorder declarations; empty output; drop a comment in a pass | **high** | planned (T4 to T6) | yes, with `meaning` over 94 kinds |
| P3 | idempotence | F6 | append a blank line each run | **high**: three tickets, found only by fuzzing | planned | yes |
| P4 | comments kept, between texts | F3, F5 | drop or reorder comments anywhere, the parser included | **high**: the one silent loss | (a) 8, in T3 already; (b) 15 to 25 and a conjunct in about 50 walk lemmas; (c) 10 to 15; glue 3. About 25 min | yes: replaces `check::same_comments` |
| P5 | rule N's reach | F4 inside parsing | settle every comment at the top of the file | **medium-high**: closes the last hole P4 leaves | 10 to 15, 10 min, in T3 | yes: `tidy.rs`'s rule N is the same rule |
| P6 | blank lines, doc comments | none seen | a parser that forgets blank lines | **low** for Toy++; doc comments medium for the real one | blank lines 10 to 15; doc comments n/a | doc comments: yes, through P2 |
| P7 | output depends only on the tree | F7 | **identity**; keep the author's breaks | **high for its cost** | 1 | yes, as a design rule: the printer reads no white space |
| P8 | normal form for `meaning` | F7, a pass that forgets to tidy | a pass that does nothing | medium; constrains every later pass | false today; 30 to 60 once the passes are made exact | no: the Rust passes are conservative the same way |
| P9 | code tokens kept, between texts | F9, F5 for `meaning` | anything a too-forgetful `meaning` would let through | **medium**: defence in depth | 30 to 45, 40 min | yes: replaces `check::same_tokens` |
| P10 | width | F10 (part) | one line for everything; break everywhere | medium | 40 to 80, new engine theory, 60 to 90 min, uncertain | hard |
| P11 | totality | F11 (part: no loop, no panic) | loop forever | high, and free | 0: the type says it | yes, once written in Stitchwort |
| P12 | tidy output | none seen | trailing spaces | **low** | 10 to 20 | easy, low value |
| P13 | locality | none seen | align across declarations | **low** now | 5 to 10 at tree level; 30+ at text level | tree level only |
| P14 | input that doesn't parse | F8 (reported, not written) | "fix" broken input | medium | 1, by computing | yes |
| P15 | silly formatters as a file | F5 | vacuous statements | **high for its cost** | 8 to 12 examples, 10 min | yes: same file, Stitchwort syntax |

**Better left as tests:**

- **Goldens:** F10 (which layout is chosen), P12, the style sheet. A
  proof would only restate the rules.
- **The disturber and the fuzzers:** P8 (same meaning, same output), P6's
  blank lines, P13, and `meaning` itself against a second opinion (for
  Stitchwort, the declaration hashes, `fmt_hashes`).
- **Deep and large inputs:** F11's stack and time.
- **`Files.simulate` tests:** F12 and P14's driver half (the toy has the
  write-counting handler, stage C).

## 3. The degenerate-implementation check

Each row is a formatter nobody wants. "Stopped by" names the first
theorem it breaks; "admitted" means the set can't tell it from a good
one.

| Silly formatter | Planned three (P1 to P3) | Must set (§4) | Must + P9 |
|---|---|---|---|
| Returns its input unchanged | **admitted** | stopped by P7 | stopped |
| Parser or rule N drops every comment | **admitted** (T0) | stopped by P4 | stopped |
| A pass drops a comment | stopped by P2 | stopped | stopped |
| Rule N keeps every comment but moves them all to the top | **admitted** | stopped by P5 | stopped |
| Reorders declarations, or comments | stopped by P2 | stopped (P2, P4) | stopped |
| Refuses every file | stopped by P1 | stopped | stopped |
| `meaning` forgets something (an operator's sign, say) and a pass changes it | **admitted** | **admitted**; P15's examples show the common cases distinct | stopped for anything that is a token |
| The parser forgets blank lines | **admitted** | **admitted**; goldens catch it | admitted |
| Breaks at every place it may | admitted | **admitted**; goldens | admitted |
| Puts everything that still parses on one line | admitted | **admitted**; goldens | admitted |
| Tidies only some of the time (a pass that skips odd cases) | admitted | **admitted** when the skipped case is in the tree; the disturber | admitted |

So the must set still admits three kinds: a wrong `meaning`, a parser
that forgets blank lines, and bad but lawful layout. The first is the
only one that could lose a user's code, and it is why P9 is the first
thing to add if the surface grows.

## 4. A recommended surface

**Must** (every observed failure class that a theorem can cover):

| Theorem | Covers | New to the plan? |
|---|---|---|
| P1 `formatAnswers`, `formatRoundTrip`, `printParses` | F1, F8, F9 | planned |
| P2 `formatKeepsMeaning` | F2, F4, F9 | planned |
| P3 `formatIdempotent` | F6 | planned |
| P4 `formatKeepsComments`, between texts | F3, F5 | (a) stated by T0; (b), (c) and the end-to-end statement are new |
| P5 `settledNear` | F4 inside parsing | new |
| P7 `formatSameTree` | F7 | new, one line |
| P14 the `ParseError` half | F8 | new, one line |
| P15 `Degenerate.sw` | F5 | new, examples only |
| P11 totality | F11 (part) | free |

**Worth considering,** in order: P9 (code tokens between texts); P6's
text-level blank lines; P13 at tree level.

**Test, don't prove:** P8, P10, P12, P13 at text level, F10, F11's
depth, F12.

**The delta to Toy++'s stages,** against T0's revised times [estimated]:

| Stage | T0's estimate | Adds | New estimate |
|---|---|---|---|
| T3 rule N | 2 × 50 min | P5 (10 to 15 lemmas); P4's parser half (b) (15 to 25, and the walk conjunct) | 2 × 62 min |
| T4 pass frame | 30 min | P4 (c) and its end-to-end statement (13 to 18); P7 and P14 (2) | 40 min |
| T5 P3 | 50 min | nothing: each pass's comments come through `meaning` | 50 min |
| T6 P4 | 20 min | nothing | 20 min |
| T7 close | 20 min | P15 (8 to 12 examples) | 30 min |
| **T3 to T7** | **3 h 40 min** | **40 to 60 lemmas, about 10 examples** | **about 4 h 25 min** |

P9, if chosen, is a stage of its own after T6: 30 to 45 lemmas, 40
minutes, with a stop at 60. It should come after P4, which builds the
same kind of statement for comments.

One caution on (b). It adds a conjunct to about 50 walk lemmas in the
riskiest stage. If T3 runs long, (b) can move to T7 without changing any
other statement; P4 then waits for it.

## 5. Decisions for Matt

**1. Is the must set above Toy++'s proof surface?** [rec: yes]

*The problem.* The three planned theorems admit a formatter that returns
its input, one whose parser drops every comment, and one that moves
every comment to the top of the file. The real formatter has already
shipped the second (SW-3606).

*The change.* Four additions: every comment kept, stated between the two
texts through the lexer only (P4); rule N moves a comment only past
closers and commas (P5); the output depends only on the tree (P7, one
line); and a checked file of silly formatters, each breaking a named
theorem (P15). This replaces T0's D candidate 1: the parser's half moves
from a stretch to part of the plan.

*What it should do.* Each failure class of §1 is covered by a theorem,
except style (F10), stack and time (F11) and the driver (F12), which
stay tests. About 45 minutes more agent time on T3 to T7 (3 h 40 min to
about 4 h 25 min) [estimated].

**2. Should "the code tokens are kept" (P9) be proved in Toy++ as
well?** [rec: not now; decide after T6]

*The problem.* `meaning` is the one definition every pass theorem rests
on and nothing proves. If it forgot something, a pass could change that
thing and every theorem would still hold. A token-level statement
doesn't use `meaning` at all, and it is what would let the real
formatter drop its run-time token check.

*The change.* One more stage after T6: about 40 lemmas, 40 minutes
[estimated].

*What it should do.* A second, independent guarantee for code, as P4 is
for comments. I'd wait because no observed failure needs it (the tree
check has caught every wrong program so far), P15's examples guard the
common ways `meaning` could be wrong, and after P4 its cost will be
known and not estimated.

Not Matt's, for the orchestrator: T0's D candidate 2 (same meaning, same
output: test it, and make P1 exact) stands as T0 put it, with P7 as the
part that is proved; the T3 and T4 briefs should name P4, P5, P7 and P14;
T7's brief should name P15.

## Findings worth tickets

- `check::same_tokens` treats any two tokens whose texts both hold a
  line break as the same text, relying on the token kind's equality to
  compare a text block's value (`check.rs:28`) [checked by reading; not
  run]. Worth one unit test that two different `"""` blocks are refused.
- The fuzz minimals are in a session scratchpad. T0 turned 12 into
  `tools/toyfmt/plus/inputs/`; the other 15 exist only as fmt unit tests'
  inputs, if the fixing lanes added them all. Worth checking each of the
  27 is a named test.
