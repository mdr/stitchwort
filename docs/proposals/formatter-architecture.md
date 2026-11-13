# The formatter's architecture: tokens and lines, or a pretty printer from a tree?

**Status:** comparison, 13 November 2026 (SW-3152, for D3557). Paper lane:
nothing is built. It stops for Matt's decisions ([§8](#8-questions-for-matt)).

Claims are marked **[measured]** (run for this note at `0ddea4026`, over the
1,825 tracked `.sw` files outside `examples/reject`, `examples/soundness` and
the formatter's golden files), **[source]** (read in the code), **[probe]**
(a scratch file through the release binary's `fmt`, [Appendix A](#appendix-a-the-probes)),
**[estimated]**, or **[from memory]** (how other tools work: I did not
recheck their sources for this note).

## In plain words

**The problem.** `stitchwort fmt` tidies indentation and spacing but leaves
every line break where the author put it. So the same code written five
ways stays five ways, and nothing ever wraps a long line: one code line in
ten is over 120 characters [measured]. Agents write most of the code, and
each lays things out a little differently. Matt asks whether the formatter
should instead parse the file and print it afresh from the syntax tree, as
most formatters do.

**What I found.** That is two questions, and they come apart:

1. *Who chooses the line breaks:* the author (today) or the formatter (one
   layout for each piece of code). This is the part you see.
2. *What the formatter works from:* tokens and line columns with the parser
   as a referee (today), or a syntax tree. This is the part you don't see.

A formatter that chooses line breaks well has to know the code's structure:
which brackets hold arguments, where a pipeline's stages are, what binds
tighter. Today's formatter doesn't have that; it would have to rebuild it
from tokens, which is writing a second parser inside the formatter. So if
the answer to 1 is "the formatter", the answer to 2 is "a tree". If the
answer to 1 is "the author", today's design is the right size and a tree
buys little.

**The recommendation.** Let the formatter choose the line breaks, from a
tree. The tree is a second output of the parser we have (same parse, no
second parser, compiler unchanged), with every token and comment in it. The
layout engine is the standard one (Wadler's, as in Prettier), which
`crates/fmt/src/doc.rs` already contains unused. The safety check stays: the
output must have the same tokens, comments and tree as the input, or the
declaration is left as written.

**What it should do.** One layout for each piece of code whoever wrote it;
no code line over 120 except where a string or name can't be split (today:
8,221 lines over) [measured]; quick fixes and sweeps that no longer need to
lay out their own output. Cost: about 45–70 lane hours [estimated], most of
it on Opus, and a reformat of the whole repo (which doesn't count, D2303).
The classic risk, losing or misplacing comments, is small here: 99% of
comment lines sit between declarations [measured].

## 1. The options

**A. Today's design, improved.** Tokens and lines [source: `crates/fmt`,
2,078 lines]. The author's line breaks are kept (D1013). A line's
indentation comes from how the lines' columns compare; spacing from a table
of token pairs. The parser referees: output must parse to the same tree.
Where one layout is wanted, a rule is added by hand on the tokens: comma
brackets (D1012), `:= match` (D3553), `∀` in theorem headers (D3472),
redundant parentheses (SW-2691). Each declaration is tried up to four ways
until one passes the check. "Improved" means more such rules, one construct
at a time.

**B. A pretty printer from a tree.** Parse to a tree that keeps every token
and comment; turn each node into a layout document ("these parts go on one
line if they fit in 120, otherwise one per line, indented 2"); print it.
The author's line breaks are not consulted, except blank lines between
statements and declarations (kept, runs collapsed to one, as today).

**A middle option, tree in and author's breaks out** (gofmt, Ormolu, Roslyn),
is possible but poor value: it pays for the tree and still gives five
layouts for one pipeline.

### What the well-known tools do [from memory]

| Tool | Works from | Who chooses line breaks | Comments |
|---|---|---|---|
| gofmt | syntax tree (not lossless) | mostly the author: no line width, blank-line runs collapsed | a side list, placed by position |
| rustfmt | compiler's tree (not lossless) | the formatter, width 100 | recovered from the source text between nodes; code it can't fit is left alone |
| Prettier | syntax tree | the formatter, width 80; a few author hints (a blank line; an object written open stays open) | attached to the nearest node before printing |
| Black | lossless tree (blib2to3: each token carries the whitespace and comments before it) | the formatter, width 88; a trailing comma is a hint to keep a bracket open | on the tokens |
| Ormolu | compiler's tree | no width; each node is one line or several, as the author had it | from the token stream, by position |
| Roslyn's formatter | lossless tree | mostly the author: it adjusts the whitespace between tokens | trivia on tokens |
| rust-analyzer | lossless tree (rowan) | does not format: it calls rustfmt | on the tree |
| clang-format | tokens, guessing the structure | the formatter, by penalty search | tokens |

Two things stand out. Nearly every formatter that chooses line breaks works
from a tree; clang-format is the exception, because C++ can't be parsed
without the compiler, and its structure guesses are a known source of bugs.
And a lossless tree does not by itself give a formatter: rust-analyzer has
the best-known one and still calls rustfmt.

## 2. What code looks like

"Today" is real output [probe]. "B" is a **hand-written mock-up** under the
rules I'd propose (a group goes on one line if it fits in 120, otherwise
each part gets a line; +2 for bodies and arguments, +4 for header lines).
Each mock-up has the same tokens as its original and parses [probe]; the
real rules for each construct are stage 0's job ([§6](#6-staging)).

**Pipelines.** All five of these are fixed points of today's formatter
[probe]; the first is how `aoc/` writes them:

```text
def a (turns: List Nat) (start: Nat): Nat :=        def b (turns: List Nat) (start: Nat): Nat :=
  turns                                               turns |> .map (x => x + start) |> .drop 1
    |> .map (x => x + start)                            |> .sum
    |> .drop 1
    |> .sum                                         def c (turns: List Nat) (start: Nat): Nat := turns |> .map (x => x + start) |> .drop 1 |> .sum
```

and the same again as nested calls, broken in two different places. B
prints `a`, `b` and `c` identically (as `a`, under the rule in D3560).

**A theorem with a long header and a long call**
(`aoc/src/Aoc/Year2020/Day09/Proofs/ParseComplete.sw:26`). Today, kept as
written, 138 and 168 characters:

```text
theorem writtenUnique ∀ (chars: List Char) (a: Nat) (b: Nat) (writtenA: NumberWritten chars a) (writtenB: NumberWritten chars b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (Parse.runsRun Parse.nat chars a (runsNumber chars a writtenA))) (Parse.runsRun Parse.nat chars b (runsNumber chars b writtenB)))
```

B (mock-up):

```text
theorem writtenUnique ∀
    (chars: List Char)
    (a: Nat)
    (b: Nat)
    (writtenA: NumberWritten chars a)
    (writtenB: NumberWritten chars b):
    a = b :=
  Result.okInjective
    (Eq.trans
      (Eq.sym (Parse.runsRun Parse.nat chars a (runsNumber chars a writtenA)))
      (Parse.runsRun Parse.nat chars b (runsNumber chars b writtenB)))
```

The theorem below it in the same file breaks its header after the fourth
parameter, at 139 characters; B gives both the same shape. 3,299 of the
over-long lines are first lines of declarations [measured].

**`match` with a record in a long arm**
(`aoc/src/Aoc/Year2021/Day18/Spec/Spec.sw:58`). Today the first arm is one
line of 157 characters. B (mock-up):

```text
def explodeLeaves (leaves: List Leaf): Option (List Leaf) := match firstDeep leaves with
  | Some found =>
    Some
      (addToLast found.left.value found.before
        ++ [{ value = 0, depth = found.left.depth - 1 }, ..addToFirst found.right.value found.after])
  | None => None
```

**`calc`** (`aoc/src/Aoc/Common/Proofs/Range.sw:32` and `:57`). Today, two
steps laid out two ways by their authors, both kept:

```text
    _ = Succ (Succ r.to - Nat.max r.from (Succ s))        _ = 0 := List.occurrencesNone ids
      := rewrite countFrom r c (Succ s) omega               (id => r.contains id)
                                                            (id =>
                                                              match t: Nat.leq r.from id with …
```

B (mock-up): a step is `_ = right := proof` on one line if it fits;
otherwise the proof goes below, and its arguments are all on one line or
all on their own:

```text
    _ = Succ (Succ r.to - Nat.max r.from (Succ s)) := rewrite countFrom r c (Succ s) omega

    _ = 0 :=
      List.occurrencesNone
        ids
        (id => r.contains id)
        (id =>
          match t: Nat.leq r.from id with
            | True => Nat.leqFalseOfLess r.to id omega
            | False => rfl)
```

**Comments in awkward places.** Both designs give the same result [probe
for today; mock-up for B]: a comment ends its line, so whatever holds it
must be printed broken.

```text
def h: List Nat := [1, 2, -- two        def h: List Nat := [
  3]                                      1,
                                          2, -- two
                                          3
                                        ]
```

A comment between arms stays between them. The difference is what happens
in a place no rule expects (after a function's name and before its
arguments, say): A keeps the line as it is; B must have a rule, or leave
that declaration as written ([§3](#3-the-comparison), risks).

**Text blocks and long strings.** The same in both: a `"""` block moves as
one piece and is never re-flowed, and a string is never split. A long
`test "…" := …` line in B has its body moved below the header; 774 of the
over-long lines hold a string [measured] and some will stay long.

**What B gives up.** A proof laid out on purpose (a staircase of
`Eq.trans`, a grid of numbers in rows) gets the standard layout. Matt
already chose that for brackets (D1017: no exception for literal rows).
And a small edit can re-wrap the group it sits in, so diffs are sometimes
wider than the change.

## 3. The comparison

| | A: tokens and lines | B: printer from a tree |
|---|---|---|
| **Consistency of agent-written code** | Spacing and indentation only. Each further piece costs a hand-written rule; four so far. Long lines grow: 8,221 code lines (10%) over 120, 863 over 160 [measured]; D1014's width is not enforced | One layout per piece of code. The width is enforced where the code can be split |
| **Tooling** | Tools edit text, then call `fmt`, which keeps whatever line breaks the tool made, so each tool does its own layout. "Add missing arms" finds the arms by scanning lines for `\| ` at a column [source: `crates/lsp/src/arms.rs`]; the binder sweep reads the tree and the tokens side by side and lays out "roughly" [source: `binder_sweep.rs`] | Tools can produce any text, or new tree nodes, and the printer lays it out. A tree with every token gives "the arms of this match", "this binder's brackets" directly. Rename is unaffected (it works from the checker's names) |
| **The parser** | Unchanged | Gains a second output: [§4](#4-the-tree) |
| **Code that doesn't parse** | Refused whole (D1021). Could format the good declarations and copy the broken one | The same, and the same possible improvement. A tree doesn't help with half-typed code unless the parser also builds error nodes, which I don't propose |
| **Safety** | Same tokens, comments and tree, checked on every run; a failing declaration is retried more simply, then copied | The same three checks, per declaration and per file; a failing declaration is copied as written and counted (the count over the repo is tested to be 0, as today) |
| **Idempotence** | Known only from fuzzing; bugs were found as late as 10 November (SW-2466) | Follows from the round trip: if printing depends only on the tree, and the output parses back to that tree, formatting twice equals formatting once. Still fuzzed |
| **Speed** | 7.9 s for the tree, of which about 1 s is real work and the rest is comparing trees by printing them as text (SW-3145's finding); 0.27 s for 151 KB of std [measured] | About the same [estimated]: building the tree and a linear-time printer replace the line passes. The tree comparison is the cost in both, and its fix is the same ticket |
| **Cost** | Nothing now; 2–6 lane hours a rule after that, each re-deriving structure from tokens, with a retry ladder that grows (4 layouts tried now) [estimated] | 45–70 lane hours [estimated], [§6](#6-staging) |
| **Main risks** | The style never converges; `layout.rs` (1,356 lines, synthetic columns, role tables) gets harder to change with each rule | Comments; ugly output on some proof shapes until the rules are tuned; a layout-sensitive grammar, where a wrong column changes meaning (the check catches it, and Ormolu shows it can be done for Haskell) |

**On comments,** the classic hard part: Stitchwort has only line comments,
so a comment always ends a line and there is no "comment in the middle of
a line" case. Of 28,315 own-line comment lines, 28,119 are at column 0,
between declarations; 196 are inside a body (between arms or statements,
mostly); trailing comments number a few dozen, most on constructors and
fields [measured, by pattern]. So three rules cover nearly everything:
before a declaration, before an arm or statement or bracket element, and
after a line's last token. The check refuses to lose a comment, so the
worst case is a declaration left unformatted, not a comment lost.

## 4. The tree

**What the parser keeps today** [source]. The lexer drops comments;
`lex_with_trivia` gives them back per token (own-line comments before,
blank lines before, one trailing comment). The syntax tree is the
compiler's: it has no node for most brackets, nests tuples, turns `let
(a, b) = e` into a `match`, gives chained comparisons a hidden name, and
has no span on applications, operators or pipes. It cannot be printed back.

**What B needs:** a tree whose leaves are the tokens (with their comments)
and whose nodes say what construct they are: a *lossless* tree.

**How to get it, three ways:**

1. *Rewrite the parser to build the lossless tree, and derive the
   compiler's tree from it* (rust-analyzer, Roslyn, Swift). One tree
   feeds everything. It rewrites how 5,470 lines of parser [source] build
   their results, and every diagnostic position passes through it.
2. *A second parser for the formatter.* Two grammars to keep in step.
   No.
3. *The same parser, a second output.* Each parsing function marks where
   its construct starts and ends in the token list ("a match starts at
   token 40", "ends at 97"). The marks, with the tokens, are the lossless
   tree. The compiler's tree is built exactly as now; the marks are
   recorded only when asked for. It is the same parse, so the two trees
   cannot disagree. This is rowan's event technique added to the existing
   parser, which has about 340 parsing functions. I found no place where
   it moves its position backwards [source: a search, not a full read],
   so marks should never need undoing.

I recommend 3. For users the end states of 1 and 3 are the same; 3 keeps
tree-building out of the compiler's normal path, and leaves 1 open later
(the marks are the first half of it). Test: for every file, the tree's
tokens and trivia, read left to right, are the file.

**Who else uses it.** The quick fixes and sweeps, to find and replace
constructs without scanning text; "format this declaration" in the LSP;
later, structural selection and folding. The compiler does not.

## 5. Recommendation

**B, with the tree as a second output of the parser.** The reasons, in
order:

1. Consistency is the stated need, and A reaches it one hand-made rule at
   a time, each rebuilding structure the parser already has. Four rules in
   three weeks is the pattern; the pipelines, calls, headers, `if`s and
   `calc`s above are the queue.
2. The width Matt chose (D1014, 120) can't be enforced by A at all without
   that structure. D1013 was answered "(c): keep the author's breaks in
   v1, wrapping later"; B is that "later".
3. The risk that usually argues against it, comments, is unusually small
   in this language and this code.
4. The safety net carries over unchanged, so a gap in B's rules costs one
   unformatted declaration, never a wrong program.
5. It makes the formatter a function of the tree, which is what makes
   idempotence, and later a proof, tractable.

If Matt prefers to keep the author's line breaks (D3558 "no"), stay with A
and build no tree: the middle option pays most of B's cost for none of
what shows.

## 6. Staging

Lane hours are [estimated].

| Stage | What | Gate | Model | Hours |
|---|---|---|---|---|
| 0 | Style sheet (paper): the rule for every construct, each with a real before and after, and the comment rules. Stops for Matt | Matt's sign-off on the samples | Opus | 3–4 |
| 1 | The tree: marks in the parser, the lossless tree type, trivia on its leaves | Every file's tree reads back as the file; the compiler's tree and every hash unchanged; parse time with marks off unchanged | Opus (parser) | 15–25 |
| 2 | Printer core: declarations, headers, bodies, blocks, arms, brackets, comments, text blocks. A construct without a rule yet is printed as written, re-indented, and counted | The three checks and idempotence over the repo; the count reported | Opus | 10–15 |
| 3 | Every remaining construct (two or three lanes: expressions and patterns; proofs: `calc`, `rewrite`, `induct`; types, abilities, sections) | Count of unruled constructs and of declarations left as written both 0 over the repo; fuzz clean | Sonnet | 10–15 |
| 4 | Dry run: the diff's size by folder and 30 sample hunks for Matt; rule fixes from his comments | Matt's sign-off | Sonnet | 4–8 |
| 5 | Switch over: reformat the repo, delete the line-based layout, update the guide. The API, LSP and playground calls don't change | `fmt_repo`, hash snapshots unchanged | Sonnet | 2–3 |
| 6 | Later, each its own ticket: "add missing arms", the `∀` quick fixes and the binder sweep onto the tree | Their existing tests | Sonnet | 2–4 each |

Today's formatter stays in use until stage 5. Stage 1 is useful to the
tools even if the rest stopped.

## 7. What it means for the Stitchwort formatter (SW-3145, D3556)

- **Which is the better test of the language.** They test different
  things. A port of today's design is index passes over arrays, hash maps
  and synthetic columns: a test of imperative code and raw speed. B is a
  parser that builds a tree, a fold from tree to document, and Wadler's
  printer: algebraic data, pattern matching, structural recursion. That is
  the kind of program Stitchwort is for, the classic one in its family,
  and the one a reader would want to see. Both need the lexer and the
  parser, which are most of the code either way.
- **Which is easier to make byte-identical.** B [estimated]. Its output is
  one function of the tree, written down as a rule per construct, and the
  printer is about 150 lines with a published algorithm. A's output
  depends on a ladder of retries decided by the referee, on byte columns
  and on tie-breaks between sibling groups; SW-3145's own note calls it
  "all or nothing on details". B's cost is that the parser comes first,
  not last, so there is no useful stage without it.
- **Which is easier to prove things about.** B. "Printing a tree and
  parsing it gives the tree back" is a real theorem, provable construct by
  construct, and idempotence follows from it. A's honest theorems are
  about its checks, not its layout.
- **A moving target.** If B is built, a port of A is a port of code about
  to be deleted.

So: SW-3145's stages 0 and 1 (the comparison harness and the lexer) are
the same under both and can start now. The rest waits for B's stage 3,
then mirrors B, with the tree and printer in place of the line passes
[estimated: a similar 26–39 hours, the parser moving from last to second].

## 8. Questions for Matt

**D3558: should `fmt` choose the line breaks?** *The problem:* the same
code survives formatting in many layouts, and one code line in ten is over
120. *The change:* the formatter decides every line break from the code's
structure and the 120 width; it keeps only the author's blank lines.
*What it should do:* one layout per piece of code; this replaces D1013's
"keep the author's breaks in v1". Proofs laid out by hand get the standard
shape. **[rec: yes]**

**D3559: where does the tree come from?** The existing parser gains a
second output that records every construct's tokens (option 3 in §4); the
compiler's tree and the compiler are untouched. The alternative rewrites
the parser so the compiler's tree is derived from the new one. **[rec: the
second output]**

**D3560: two style rules the rest hang on** (the others come with samples
at stage 0):
(a) *Author hints:* none beyond blank lines. No "a trailing comma keeps
this open" (Black) or "written open stays open" (Prettier): each hint is a
second layout for the same code. **[rec: none]**
(b) *Pipelines:* one line if there is a single `|>` and it fits; two or
more stages always go one per line, as `aoc/` writes them now. The
alternative is "one line whenever it fits", which would join most of
today's short pipelines. **[rec: two or more stages break]**

**D3561 (answers D3556): the Stitchwort formatter.** Start its harness and
lexer now; build the rest as a port of B once B's rules are settled, not
as a port of today's design. **[rec: yes]**

## Findings worth tickets

- `fmt` spends about 85% of its time comparing trees by printing them
  (SW-3145's finding); the fix helps both designs.
- D1014's 120 width is not enforced or reported anywhere: 8,221 code lines
  are over it, 863 over 160.
- "Add missing arms" (`crates/lsp/src/arms.rs`) finds arms by scanning
  text lines for `| ` at a column, which lines of a `"""` block could
  fool [not tested]. A use for the tree (stage 6).
- `docs/proposals/formatter.md` §2.3 says the formatter walks tokens
  "using the AST to know which construct each token belongs to"; as built
  it uses columns and token roles, and the tree only as referee. The note
  could say so.

## Appendix A: the probes

In the lane's scratchpad, with `target/release/stitchwort fmt -`:

- **`p1.sw`:** one pipeline written three ways and as nested calls two
  ways; a `match` on and off the header line; a list with a trailing
  comment inside; two `if` layouts. Output: only the `match` (D3553) and
  the list (D1012) changed; the five pipeline layouts and both `if`s came
  back as written.
- **`o1.sw` and `m1.sw`:** the §2 snippets as they are in the repo, and my
  B mock-ups. Both files are fixed points of today's formatter, and with
  spaces and newlines removed they are the same text, so the mock-ups have
  the originals' tokens and parse. Whether they parse to the *same tree*
  was not checked (there is no command for it); the indentation follows
  the rules the originals use.
- **Counts:** `awk` over the 1,825 files: 133,330 lines, 82,696 of them
  code; line lengths; comment lines by column. Trailing comments were
  counted by pattern and are approximate.
- **Timing:** `fmt --check` on `List/SortLemmas.sw` and `Set/Spec.sw`
  (151 KB), one run, 0.27 s.
