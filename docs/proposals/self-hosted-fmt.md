# A Stitchwort formatter written in Stitchwort

**Status:** second plan, 14 November 2026 (SW-3228), replacing the first
(SW-3145, 13 November), which planned a port of the old token-and-line
formatter. That formatter has since been deleted, so the first plan is kept
only as history, in [Appendix B](#appendix-b-the-first-plan-superseded);
[What changed](#what-changed-since-the-first-plan) says which of its parts
still hold. Paper lane: nothing is built. The probes were throwaway `.sw`
files run with the main checkout's release binary
([Appendix A](#appendix-a-the-probes)). It stops for Matt's decisions
([§10](#10-questions-for-matt)).

Claims are marked **[measured]** (run for this note on Speedwell, load 5–10,
one run each, so rough), **[source]** (read in the code at `fb4841cf3`) or
**[estimated]** (my reasoning, not tested).

## In plain words

**The problem.** We want a demanding, real program written in Stitchwort, to
find out where the language is slow or awkward, and a formatter is a good
one. The first plan was written against a formatter that no longer exists.
`stitchwort fmt` is now a lexer, a parser that builds a tree holding every
token and comment (the lossless tree), and a printer that walks that tree and
chooses every line break itself. A Stitchwort version has to match that one,
byte for byte.

**The change.** A new project, `tools/fmt/`, that is the same three parts in
Stitchwort, built in seven stages, each compared with the Rust formatter by
one command:

1. *A lexer* that gives the same tokens and comments.
2. *A parser* that gives the same lossless tree. It is hand-written, follows
   the Rust parser function by function, and builds the tree directly; it
   does not copy the Rust parser's "marks" technique, which exists for
   reasons that don't apply in Stitchwort ([§3](#3-parsing)).
3. *A printer*: the layout engine and the rule for each construct, ported
   from `crates/fmt/src/printer/`.
4. *The safety check*, which changes: the Rust formatter checks its output
   by comparing compiler's trees, and a Stitchwort program can't call the
   Rust code that builds those. It compares lossless trees instead, which is
   at least as strict ([§3.4](#34-the-safety-check)).

Every function is total: no `Partial`.

**What it should do.**

- Format the 1,461 files `stitchwort fmt` formats in the repo (6.5 MB) to
  the same bytes, and refuse the same broken files.
- Take about 20 s for all of them in one process [estimated, range 12–30 s].
  The Rust formatter takes 8.3 s [measured], of which about 1.1 s is real
  work and the rest is one avoidable cost that is still there (SW-3147,
  comparing trees by printing them as text). So about 2–3 times today's Rust
  formatter and 10–25 times its real work, inside the Python-like target.
- Cost about 40–60 lane hours [estimated], against the first plan's 26–39:
  the printer is twice the code the old line formatter was, and the parser
  now has to produce exactly the Rust parser's tree, not just agree on
  whether a file parses.
- Give two theorems cheaply that the first plan could not: every output it
  returns parses back to the tree it was printed from, and formatting that
  output again changes nothing. Both hold by construction, at about no cost
  in run time ([§7](#7-proofs)).

**Self-hosting.** The lexer, tree and parser are exactly what a Stitchwort
parser for Stitchwort itself would start from, and the plan keeps that door
open at no extra cost. I don't recommend planning beyond that yet
([§9](#9-towards-self-hosting-a-direction-not-a-plan)).

## What changed since the first plan

| First plan (13 Nov) | Now |
|---|---|
| The Rust formatter works on tokens and lines and keeps the author's line breaks; mirror that (its §1, §2, Q1) | **Replaced.** D3558: `fmt` chooses the line breaks. The line formatter (`layout.rs`, `doc.rs`) is deleted (SW-3194, stage 5 of the tree printer). The twin mirrors the tree printer: [§1](#1-what-is-being-matched), [§2](#2-the-design) |
| The parser comes last, as a referee, and its tree has no need to match anything (its §2, stage 4, Q2) | **Replaced.** The parser comes second and must give the Rust parser's lossless tree node for node; there is no useful formatter without it. Q2 is no longer a question |
| The corpus is already formatted, so the test needs disturbed input (its §4) | **Still true**, and easier: the printer ignores the author's line breaks, so any re-layout of a file is a test, and the whole repo as it was before the reformat is in git ([§6](#6-the-comparison-harness)) |
| Widths are counted in bytes | **Replaced.** The engine counts characters: `∀` is one column [source: `engine.rs`, E5] |
| The safety check is "same tokens, comments and tree", the tree being the Stitchwort parser's own | **Changed in kind:** [§3.4](#34-the-safety-check) |
| Lexer design, arrays and index passes, fuel for the parser, the batch stream for files (its §2, Q3) | **Kept**, re-measured ([§5](#5-speed)) |
| About 20 s for the tree; target under 30 s (its §3, Q5) | **Kept**, on new measurements |
| Proofs: theorems about the checks; idempotence only by formatting twice (its §5) | **Better now:** [§7](#7-proofs) |
| Stages 0–5, 26–39 lane hours (its §6) | **Replaced:** [§8](#8-stages), 40–60 |
| Once identical, no merge gate (Q4) | **Asked again** as D3577 |

Decisions since: D3558 (the formatter chooses line breaks), D3560 (no author
hints; pipelines fit or break), D3562 (one lossless tree, the compiler's
tree lowered from it), D3561 (this project waits for the Rust formatter to
be rebuilt on the tree, then ports that design). The wait ended today: the
tree printer is `stitchwort fmt` (SW-3194), and the parser builds only the
lossless tree, with the compiler's tree lowered from it (SW-3207 to SW-3214).

## 1. What is being matched

### The Rust formatter today [source]

For each file (`crates/fmt/src/printer/mod.rs`, `print_file` and
`format_tree_in`):

1. Lex with trivia. Each token has its own-line comments before it, the
   blank lines before it, and a trailing comment.
2. Parse and lower the whole file; refuse it on any error (D1021).
3. Three rewrites, each made on the text and checked on its own: `∀` after
   a theorem's name (D3472), redundant parentheses dropped (D2307,
   `parens.rs`), neighbouring parameters of one type merged (D3565,
   `merge.rs`).
4. Parse the rewritten text to the lossless tree.
5. Per declaration: the rule for each node gives a layout document
   (`rules.rs`), the engine prints it in 120 columns (`engine.rs`), and the
   result is checked against the declaration as written: the same tokens
   (commas and parentheses aside), each comment on the same token, the same
   compiler's tree. A declaration that fails is left as written and
   counted. So is one with a comment no rule places.
6. Check the whole output the same way.

Over std, `aoc/src` and `games` (760 files, 15,829 declarations) no
declaration is left as written and no construct lacks a rule [measured:
`dev fmt-tree`].

### Its size [source, lines outside tests]

| Part | Rust | Used by the twin |
|---|---|---|
| Lexer (`lexer.rs`) | 1,535 | all of it, less the long explanations of invisible characters |
| Parser (`parser.rs`, `parser/`) | about 6,150, 234 functions | the grammar; not the wording of its errors |
| Tree (`tree.rs`) | 866 | the node kinds (94) and a dump; the mark builder and the span check are not needed |
| Lowering (`lower.rs`, `lower/`) | about 4,000 | none, except its three errors ([§3.5](#35-refusals)) |
| Layout engine (`engine.rs`) | 636 | all |
| Rules (`rules.rs`) | 1,834 | all |
| Spacing (`spacing.rs`) | 263 | all |
| Rewrites and checks (`merge.rs`, `parens.rs`, `mod.rs`, `check.rs`, `lib.rs`) | about 1,080 | all, the checks redesigned |

About 12,400 lines of Rust to match, the lowering aside; I'd expect
9,000–11,000 lines of Stitchwort [estimated].

### In and out

**In:** the same bytes as `stitchwort fmt` for every file it formats,
including the declarations it leaves as written; the same refusals for
lexical and syntax errors.

**Out:** diagnostics that match the Rust ones (only "refused or not" must
agree); refusing a file for being nested too deeply (the Rust parser stops
at about 18,000 nested brackets for its stack; the twin's limit is its
fuel); the LSP and playground hooks; error recovery
([§3.3](#33-error-recovery-s1-to-s5)); replacing `stitchwort fmt`.

## 2. The design

**Mirror the Rust formatter module for module.** Its output is one function
of the tree, written as a rule per construct, so a port that keeps the same
functions in the same order is the shortest route to the same bytes, and
the easiest to keep in step when a rule changes.

| Module (namespace) | What | Mirrors |
|---|---|---|
| `Syntax.Token`, `Syntax.Lexer` | token kinds; a state machine over `List Char` giving tokens with trivia, byte offsets and columns | `lexer.rs` |
| `Syntax.Tree` | `Syntax = Leaf (index: Nat) \| Node (kind: NodeKind) (children: List Syntax)`, the tokens and their trivia in arrays beside it; a dump in `dev tree --print`'s format | `tree.rs` |
| `Syntax.Parser` | recursive descent over the token array, one declaration at a time, building `Syntax` directly | `parser.rs`, `parser/` |
| `Fmt.Doc`, `Fmt.Engine` | the layout document and its printer | `engine.rs` |
| `Fmt.Spacing` | the space-or-not table for neighbouring tokens | `spacing.rs` |
| `Fmt.Rules` | the rule for each node kind | `rules.rs` |
| `Fmt.Rewrites` | `∀`, parentheses, merged parameters, as functions from tree to tree | `lib.rs`, `parens.rs`, `merge.rs` |
| `Fmt.Check`, `Fmt.Format` | the safety check; the file driver; `main` | `mod.rs`, `check.rs` |

Choices that differ from the Rust code, and why:

- **The parser builds the tree directly** ([§3](#3-parsing)).
- **The parser's modes are arguments.** The Rust parser keeps the block
  column, `calc` depth and the like in mutable fields that it saves and
  restores around a sub-parse. Passed as an argument, a mode is restored by
  returning.
- **The rewrites are tree to tree, not text to text.** The Rust code edits
  the text and parses again to see what it did. With the tree in hand,
  "drop this pair of brackets" is "replace this `Paren` node by its child",
  and the check knows exactly which tree to expect
  ([§3.4](#34-the-safety-check)).
- **No sharing machinery.** The engine's `Doc::Shared(Rc<Doc>)` exists so
  the options of a choice aren't built twice; Stitchwort values are shared
  already.
- **The rules' side tables** (`roles`, `keep_blank`, `hoisted`, the hug
  maps keyed by token) become arrays computed before the walk, or `Map`s
  carried through it in one state record.

**Where it lives and how it runs.** `tools/fmt/`, a project with its own
`stitchwort.yaml`, the two namespaces above in one project so the parser
can be lifted out later. Built with `stitchwort build --native tools/fmt`
to one executable. `IO` still has no file access (SW-3150, unchanged
[source]), so it is a filter: one file on standard input, or with `--batch`
a stream of files, each after a header line with its path and length,
answered the same way; a small driver feeds it the file list. The project's
own files join the repo's formatted set, and the formatter formatting its
own source is a named test.

## 3. Parsing

### 3.1 What the Rust parser does now, and why [source]

The parser cuts a file into declarations at column 0 and parses each on its
own. Its parsing functions return nothing: when one finishes a construct it
records a *mark* (a kind and the token range it covered), and a builder
sorts the marks and nests them into the tree afterwards. Three things need
care in that design: an operator finds its left operand from the last mark
(`operand_start`), a construct whose kind is known late is relabelled
(`retag_last`, `widen_section`), and a failed parse leaves marks to tidy.

Marks were the right choice in Rust for three reasons: they were added
beside an existing parser as a second output; they keep the recursive
functions' stack frames small; and they let an operator wrap an operand it
has already passed without carrying it. None applies in Stitchwort. There
is no earlier parser. Frames are not the limit (native code allows 16
million pending calls [source: the guide]). And a function that returns its
operand as a value can wrap it in a node without any bookkeeping.

### 3.2 The options

| | How | For | Against |
|---|---|---|---|
| **A. Mirror the marks** | parsing functions thread a state with a list of marks; a builder sorts and nests them | line-for-line the same as the Rust code | reproduces machinery whose reasons are gone; a sort of half a million marks; the three hazards above; a state record through every function |
| **B. Build the tree directly (recommended)** | each parsing function takes the modes, the token array and a position, and returns the node and the new position | the natural shape in a functional language; "relabel" and "wrap the operand" are ordinary expressions; the tree is a plain data type to pattern-match and prove things about | the port is function for function but not line for line: each mark call becomes a constructor at the place the value is known |
| **C. Combinators over `Std.Parse`** | the grammar as combinator expressions | reads like a grammar; `Std.Parse` has proved lemmas | `Std.Parse` reads characters only (`Parse.run (input: List Char)` [source]), so it can't parse tokens without a redesign; it ran 3.7 times slower than a hand-written scanner [measured, first plan]; the grammar is layout-sensitive, with lookahead scans (is this a lambda, is this bracket a binder) that the Rust parser hand-codes, so the combinator version would be a different program accepting, we hope, the same language |
| **D. A generated or table-driven parser** | a grammar file and a generator | none here | there is no grammar file to share; columns decide where blocks end |

**B.** The Rust parser is the specification, one function per piece of
grammar, and B keeps that correspondence while dropping the part of it that
is about Rust. A handful of small local helpers ("items separated by commas
until this closer") are fine; the point is not to adopt a combinator
library as the structure.

**The test that makes this safe:** `stitchwort dev tree --print` already
prints a file's lossless tree as indented text, one line per node kind and
token [measured]. The twin prints the same, and the gate is that the two
dumps are identical for every file in the repo: 513,260 nodes in 27,583
declarations [measured]. Whatever the internal design, the tree is the
Rust parser's tree.

**Tokens in an array, read by position.** The grammar looks ahead and
behind by index (a bracket's partner, the token before this one). The same
toy parser over an `Array` with a position was a little faster than over a
`List` (1.0 s against 1.4 s on 5.3 MB [measured]). Termination by fuel, as
the first plan said: a five-function mutually recursive parser with fuel
checked first time [measured, probe 2].

### 3.3 Error recovery (S1 to S5)

Recovery (SW-1983 is S1, running now) makes the Rust parser carry on after
a syntax error and put `Error` and `Gap` nodes in the tree. For the twin:

- **It needs none of it.** The formatter still refuses a file with any
  syntax error (D1021, restated in the recovery note). So the twin's parser
  is strict: it stops at the first error and reports "refused". Recovery
  never makes a broken file acceptable, so the set of accepted files and
  their trees don't change.
- **`Error` and `Gap` nodes never reach the printer** in a file that is
  formatted, so the rules need no case for them.
- **The cost is churn, not design.** S1 to S3 edit the same parsing
  functions the twin ports. The tree dump for correct files is unaffected,
  so the gate holds; a port started before S3 lands will be read against
  code that then moves. Starting the parser stage after S3 avoids that
  (sequencing, the orchestrator's call).
- **If "format the good declarations, keep the broken one as written" is
  wanted later** (the recovery note's §5 calls it a small change), the twin
  gets it without recovery: it parses per declaration, so a declaration
  that fails is one result to keep as written. The parser's result is
  therefore a result per declaration from the start.

A parser for the compiler itself would need recovery mirrored. That is
[§9](#9-towards-self-hosting-a-direction-not-a-plan)'s concern, not this
project's.

### 3.4 The safety check

**What the Rust check does.** It lowers the input and the output to
compiler's trees and compares them (as text, which is SW-3147's cost). The
twin has no lowering.

**What the twin does: compare lossless trees.** Parse the output with the
twin's parser, and compare with the tree that was printed, after erasing
what the printer is allowed to change: where lines break, spaces, and the
commas D1012 adds and drops. Both are plain values of one data type, so the
comparison is derived equality (two parses of 1 MB and the comparison:
0.4 s [measured]).

**Why this is at least as strict.** The lowering reads only node kinds and
token texts, never layout [source: in `lower/`, the only use of a column is
a file-level check that the first token is at column 0]. So two files with
equal erased lossless trees lower to equal compiler's trees. The converse
is false (`(x)` and `x` differ as lossless trees and not as compiler's
trees), which is where the two checks part:

- **The rewrites.** Dropping brackets, merging parameters and adding `∀`
  change the lossless tree on purpose. The Rust code checks each by
  lowering before and after. The twin makes each as a function on the tree
  and checks that the printed text parses back to the *rewritten* tree. So
  it confirms that the text says what the rewrite intended (the brackets'
  content still sits in the same place, nothing else regrouped). That the
  rewritten tree means the same as the original (the lowering drops a
  `Paren` there; a merged group is the same binders) is a fact about the
  Rust lowering which the twin asserts and does not check.
- **One comma the lowering does read.** A list of one bracketed range with
  a trailing comma, `[(0 ..< n),]`, lowers differently without the comma
  (`lower/exprs.rs`, `list`), so the Rust check fails and the declaration
  is left as written [measured]. The twin's erasure must keep that one
  comma to match. It is also a small bug: see Findings.

**What catches the twin's own mistakes.** A check that uses the twin's
parser on both sides can't see a mistake that parser makes consistently.
Two things can: the tree-dump gate (the parser against the Rust parser, on
every file), and the byte comparison of outputs (the whole formatter
against the Rust one, whose check does lower).

The other two checks carry over unchanged: the same tokens in the same
order, and each comment attached to the same token (`comment_anchors`).

### 3.5 Refusals

The Rust formatter refuses on any error from the lexer, the parser, or the
lowering. The lowering raises three of its own [source]: a parameter named
twice in a header, an or-pattern that binds names, and a condition on an
arm with `()` and no body. The twin ports those three as one small pass
over the tree, so it refuses the same files. The gate is the 1,157 deliberately
unformatted files under `examples` [measured], most of them in
`examples/reject`: refused or not, file by file.

## 4. Totality and termination

| Part | How it terminates |
|---|---|
| Lexer | structural on the character list [measured, both plans' probes] |
| Declaration split, bracket partners, token roles | index passes, `decreasing tokens.size - k` |
| Parser | fuel, started at a multiple of the token count; running out is "refused". It also stands in for the Rust parser's nesting limit |
| Tree dump, erasure, tree comparison, the three lowering checks, the rewrites | structural on the tree (a function and its helper for the child list, defined together) [measured, probe 1] |
| Rules | fuel at first, the node count. Structural recursion is the aim, but the rules reach children through accessors ("the child after `:=`"), which hides from the checker that the child is part of the node. Making them structural is part of the proof stage, if wanted |
| Engine: the print loop and `fits` | fuel. The loop works through a list of pending documents and a `Concat` pushes its parts, so it is not structural; the honest measure is the total size of what is pending. Fuel first [measured, probe 1], the measure if proofs want it |
| `main` | `{IO}` only |

No `Partial` anywhere is a gate of every stage.

## 5. Speed

**The Rust side [measured].** `stitchwort fmt --check` over std, `aoc/src`,
`games` and `examples` (1,461 files formatted, 6.5 MB, 142,000 lines; 1,157
more skipped as deliberately unformatted): 8.3 s. A sample of that run has
86% of its time in the file check's `equivalence::shape` (2,993 of 3,483
samples in `check_file`), so SW-3147 (fmt's time is in comparing trees as
text) is unchanged, and the real work is about 1.1 s. Parsing the same
files to the lossless tree takes 0.15 s, and 0.22 s with the lowering.

**Probes [measured]** (`run --native`, after subtracting 0.45–0.55 s of
checking and compiling the probe; [Appendix A](#appendix-a-the-probes)):

| Probe | 1 MB of corpus | 5.3 MB as one input |
|---|---|---|
| 1a: scanner to tokens | 0.11 s | 0.66 s |
| 1b: 1a, then a bracket tree, a layout document, a Wadler-style print in 120 columns, the text joined and written | 0.43 s, 640 MB peak | not valid (see Appendix A); 5 MB of repeated input: 4.2 s, 2.5 GB |
| 1c: 1b, then lex and parse the output and compare the trees | 0.73 s | – |
| 2: scanner, then a recursive-descent expression parser with fuel (atoms, application, three operator levels) over a `List` | 0.17 s | 1.37 s |
| 3: probe 2 over an `Array` and a position | 0.18 s | 1.00 s |
| 4: probe 1b on 200 KB, 1, 5 and 25 times in one process | 0.13 s a pass | peak memory 236, 243, 243 MB |

What they say:

- Lexing and parsing scale in a straight line to 5 MB: about 0.13 s/MB to
  lex and 0.06–0.13 s/MB more for a toy parse. The Rust parser does the
  real job at 0.02 s/MB, so the toy is already 10 times slower.
- A whole toy pipeline is 0.4–0.65 s/MB.
- **Memory is given back between files** (probe 4), so one process can
  format the whole repo. Peak is set by the largest file: at about 500
  bytes per input byte, 100 MB for the largest (189 KB).
- Large single inputs still slow down more than in proportion when printing
  (10 times the time for 5 times the input), which is SW-3148 (large heaps
  slow in native code), milder than the first plan measured (23 times for
  6.8). One file at a time avoids it.

**Estimate.** The real lexer has more states than the toy, the real parser
has 234 functions, the rules build several document nodes per token and
the engine re-measures at choices. Per MB: lex 0.2–0.3 s, parse 0.3–0.8,
rules and engine 0.6–1.5, the safety check (lex, parse, compare) 0.6–1.2,
rewrites 0.1: **1.8–3.9 s per MB, so 12–25 s for the 6.5 MB; I'd plan on
20 s** [estimated].

**Proposed target (unchanged):** all 1,461 files in one process in under
30 s on Speedwell, peak memory under 500 MB, no file more than 30 times its
Rust time measured without SW-3147's cost.

### What in Stitchwort is missing or slow

Re-checked today; the first plan's tickets by number:

| | State | Effect on the plan |
|---|---|---|
| SW-3149 (native executables fail to start from the main checkout) | **Still fails** [measured: "its tables can't be read: written by a different build of the runtime"; the runtime library is from 14:28, the CLI from 15:10] | Stage 0 needs `build --native` to work, or every harness run pays the check and compile. To fix first |
| SW-3150 (IO has no file access; `Text` has no cheap slice, indexed read or builder) | **Unchanged** [source: `Text.get`, `take` and `drop` still go through `toList`] | The batch stream, and tokens built from character lists. Affordable: lexing is not where the time goes |
| SW-3148 (large heaps slow in native code) | **Milder, still there** [measured above] | None while files are formatted one at a time |
| SW-3147 (fmt's time is in comparing trees as text) | **Unchanged** [measured above] | It sets what "times the Rust formatter" means. Now that the lossless tree is the parser's output, the fix is to compare lossless trees, as the twin will |
| `Std.Parse` reads characters only | [source] | Rules out option C |
| No text patterns: `\| "def" => …` is a syntax error | [measured] | The lexer's keyword table is a `Map`, or a chain of `==` |
| Unknown until stage 1 or 2 | – | Check time for a 10,000-line project with a 234-function mutually recursive group; the cost of a `Map` lookup per token; derived equality on a 94-constructor kind type |

## 6. The comparison harness

One command, `task fmt:twin`, with a stage argument. It builds the native
executable, feeds it files in batch mode, and compares with what the Rust
side gives, printing counts and the first difference. The Rust side's
answers are written once to a cache folder outside the repo, keyed by the
input's hash and the hash of `crates/syntax` and `crates/fmt`.

| Compared | Rust side | For |
|---|---|---|
| Tokens with trivia, one line a token | a new `dev` dump (the tree dump has no trivia) | stage 1 |
| The lossless tree | `dev tree --print`, exists | stage 2 |
| Refused or not | `fmt --check`'s exit and message | stages 2 and 5 |
| The formatted text, and which declarations were left as written | `dev fmt-tree --print --verbose`, exists | stages 3 to 5 |

**Inputs.** The repo as it is only tests the fixed point (every file is
already formatted), so:

1. the 52 golden pairs (`crates/fmt/tests/it/golden`), which cover the
   rewrites and the comment cases: the lane-sized test;
2. the repo as it is (the fixed point, and all the trees);
3. **the repo as it was before the reformat:** the parent of `39de3aa7d`
   (SW-3194's reformat with the tree printer) has every file in the old,
   author-chosen layout. That is 6 MB of real unformatted input for free;
4. the formatter fuzzer's generated programs (`crates/fmt/tests/it/fuzz.rs`),
   written out by a seed;
5. a disturber, at run time from a seed: indentation scaled, spaces squeezed
   and doubled, blank lines and trailing spaces added, lines joined and
   split inside brackets, commas moved to line starts.

Nothing new is committed beyond the harness.

**Lanes and the budget.** A lane runs the goldens and a handful of named
files (seconds). The full run is a broader suite: the verifier runs it
after a merge that touches `tools/fmt`, `crates/fmt` or `crates/syntax`,
and Overmind in its rolling check.

## 7. Proofs

The new design makes two real theorems cheap, because the formatter returns
its answer only after checking it and because the printer can be given a
type that has no layout in it.

**1. Printing then parsing gives the tree back** (by validation):

```stitchwort
-- Sketch: names not settled. `erase` drops what the printer may change.
theorem formatRoundTrip ∀ (source output: Text) (h: format source = Ok output):
    (parse output).map erase = (parse source).map (tree => erase (rewrite tree))
```

It unfolds the definition of `format` and never mentions a layout rule.
About a day [estimated].

**2. Idempotence, without formatting twice.** Give the rules the *erased*
tree as their input type: kinds, token texts, comments, kept blank lines
and the few kept spaces, and nothing else. Then "the output depends only on
the erased tree" is true by typing. With theorem 1, and one more cheap
check at run time (the rewrites find nothing left to do in the output's
tree, which is already parsed), formatting the output again is printing the
same erased tree:

```stitchwort
theorem formatIdempotent ∀ (source output: Text) (h: format source = Stable output):
    format output = Stable output
```

`Stable` is the answer when the extra check passed; the gate over the repo
is that every file's answer is `Stable`. One to two days [estimated]. The
first plan could offer this only by formatting everything twice.

**3. The tree is lossless:** the tokens of `parse source`, read left to
right, are `lex source`. By validation it is a one-line check and a short
proof. From the parser's definition it is the invariant "the node's tokens
followed by what is left are what the function was given", for each of the
234 functions: mechanical and long, a week or more [estimated]. Worth it
only as a showcase.

**Not recommended:** proving `parse (print tree) = tree` from the rules,
with no check at run time. It needs, for every construct, that its printed
form reads back as that construct under a layout-sensitive grammar. Months,
and every style change would break it [estimated].

**Middle ground, each 2–5 days of Opus** [estimated]: the output is tidy
(no line ends in a space, no two blank lines in a row, one final newline),
which is a property of the engine's writer alone; a document printed flat
has no line break; the lexer's round trip.

## 8. Stages

Hours are lane hours [estimated]. Each stage ends with its harness count,
its speed numbers (seconds per MB on a fixed 1 MB sample and the three
largest files, peak memory) and friction notes in `tools/fmt/NOTES.md`.

| Stage | What | Gate | Model | Hours |
|---|---|---|---|---|
| 0 | SW-3149 fixed. The harness: batch driver, the token dump, cached Rust answers, the old-layout checkout, the fuzzer's programs written out, the disturber. Count, over all inputs, how often the Rust formatter leaves a declaration as written and how many bracket and merge candidates there are | a stub that copies its input scores 0 of N on unformatted input and N of N on the repo as it is | Sonnet | 3–4 |
| 1 | Project skeleton, token type, lexer with trivia, batch `main` | token dump identical on every file that lexes; the same files refused for lexical errors | Opus (sets the project's shape; first friction notes) | 4–5 |
| 2 | The tree type and its dump; the parser, in three lanes: expressions and patterns; declarations, headers and types; blocks, `match`, handlers and proofs. The three lowering errors | tree dump identical on every file that parses; refused or not identical on every file, `examples/reject` included | Opus for the first lane, Sonnet after | 14–20 |
| 3 | The layout engine (with the Rust engine's unit tests ported), spacing, the file driver, comments, and the rules for declarations, headers, bodies and blocks | engine tests pass; every declaration that uses only those constructs identical, counted by the harness | Opus | 6–8 |
| 4 | The remaining rules, in two lanes: calls, operators, pipelines, lambdas and brackets; `match`, handlers, proofs, types and data | identical on the repo as it is, with no rewrites and no check | Sonnet; one rule family is a fair DeepSeek trial (an exact oracle, a bounded task) | 8–12 |
| 5 | The rewrites as tree functions, the safety check, left-as-written fallbacks, refusal | identical on everything: goldens, old layout, fuzzer, disturbed; the same declarations left as written; formats its own source | Sonnet, Opus for the check | 4–6 |
| 6 | Speed pass from profiles; the friction report; a ticket for each gap | under 30 s for the repo | Sonnet, Opus for the report | 3–4 |
| 7 | Proofs (optional): theorems 1 and 2, then the rest if wanted | `task audit:touched` clean | Sonnet, Opus for the parts | 2–3 days, then open |

Stages 0–6: **42–59 lane hours**, about 17–22 of them Opus and the rest
Sonnet. Stage 2's lanes can run side by side after the first; stage 3's
engine can start beside stage 2; stage 4's two lanes run side by side.
Stages 0–2 stand on their own: they give a Stitchwort parser of Stitchwort,
tested node for node, and most of what there is to learn about the language
from this project.

**Risks.**

- *The parser is most of the work, and now it is first.* If it is slow or
  painful there is no formatter to show for stages 0–2. But it is also the
  part with the sharpest test.
- *The target moves.* `crates/fmt/src/printer` had 18 commits in the last
  two days and the parser 54 this month [measured]; recovery is editing the
  parser now. Every change needs the twin caught up (D3577).
- *Byte-identical is all or nothing on details:* which declarations are
  left as written, the kept spaces, `\r`, the last-variable rule in headers
  (SW-3193). The old-layout checkout is there to find these early.
- *Check time on a 10,000-line project* could make the edit loop slow; a
  finding, not a blocker.

## 9. Towards self-hosting: a direction, not a plan

**What this project gives.** Stages 1 and 2 are a Stitchwort lexer and
parser that produce the same lossless tree as the Rust ones, tested on
every file. In a compiler that is the first box. The design today helps
more than it did a week ago:

- The tree is one small generic type (a kind and children), with a text
  dump, so "the same tree" is a file comparison.
- Since the lowering work, the Rust parser builds nothing but that tree.
  There is no second output to match.
- The lowering "reads, never parses" and is one function per node kind
  [source: `lower.rs`]: a pure function from one data type to another,
  about 4,000 lines, which is the kind of code Stitchwort is good at and
  could be tested the same way (dump the compiler's tree from both).
- Declarations parse independently, so a Stitchwort parser and the Rust one
  can be compared, or mixed, one declaration at a time.

**What the next steps would be.** (1) The lowering in Stitchwort, with a
dump of the compiler's tree as its gate: perhaps 15–25 lane hours
[estimated]. (2) A way for the Rust compiler to call natively compiled
Stitchwort code and take a tree back, and a build that needs an earlier
`stitchwort` to build the next one. (3) Then the elaborator, which is
131,000 lines of Rust against the syntax crate's 23,000 [measured]: not a
next step in any near sense.

**Where the kernel boundary sits.** It doesn't move. The kernel
(`crates/core`, 29,000 lines) is what proofs are trusted on, and it checks
terms whoever made them, so a parser, lowering or elaborator in Stitchwort
adds nothing to what must be trusted for a proof to be valid. What the
parser and lowering are trusted for is that the theorem checked is the one
written. A Stitchwort parser could carry proofs about exactly that
([§7](#7-proofs)), which the Rust one can't. A kernel written in Stitchwort
is a different question (what checks the checker), and not on this path.

**What makes it hard.**

- *Speed.* Every `check` parses and lowers all of std: 69 ms in Rust
  [measured, lowering note]. At the 10–20 times these probes suggest, that
  is about a second added to every check. Self-hosting the parser is only
  sensible once native Stitchwort is within about 2–3 times of Rust on this
  kind of code, which needs cheap text slices and work that is paused
  (SW-3150, D3465).
- *Errors.* The compiler's parser must give the Rust parser's messages
  word for word and recover as S1 to S5 design. The formatter needs neither,
  so this project doesn't show how hard that is.
- *Two parsers until one is deleted.* The Rust one changes weekly.
- *Bootstrapping.* Today the repo builds with cargo alone.

**What would have to be true for it to be worth doing.** A reason the Rust
parser can't serve: proofs about the parser that we want, or tools written
in Stitchwort (sweeps, quick fixes) that want the tree as Stitchwort data.
The second is the likelier first user, and it needs no bootstrapping. Plus
the speed gap above, and evidence from this project that the twin stays in
step cheaply.

**So:** build the formatter's parser as its own namespace with its own
gate, keep byte offsets on its tokens, return a result per declaration, and
decide nothing further until stage 6's numbers are in.

## 10. Questions for Matt

**D3576: build it, to this plan, starting with stages 0 to 2?**
*The problem:* D3561 said the Stitchwort formatter waits for the Rust one
to be rebuilt on the tree; that is done, and the first plan no longer fits.
*The change:* a twin of the tree printer in `tools/fmt/`, 42–59 lane hours
[estimated] in seven stages; first the harness, the lexer and the parser
(21–29 hours), then a report with speed numbers before the printer starts.
The target stays "the repo in under 30 s" (about 20 s estimated; Rust
8.3 s measured).
*What it should do:* the demanding real program the project was meant to
be, with a parser tested node for node against the Rust one after the
first three stages, whatever is decided after them. **[rec: yes, stages
0–2, then report]**

**D3577: once identical, must it stay identical?**
*The problem:* the Rust formatter and parser change most days (18 printer
commits in two days). A rule that every such change also updates the twin
would slow that work.
*The change:* no merge gate. The harness runs in the rolling check and
reports drift; the twin is caught up in batches and may lag by a day or
two. The alternative makes the twin part of every formatter or grammar
lane.
*What it should do:* the Rust formatter keeps its pace; the twin's drift
count becomes the measure of what a second implementation costs, which is
the number the self-hosting question needs. **[rec: no gate]**

**D3578: self-hosting the parser: keep the door open, plan nothing yet?**
*The problem:* the twin's lexer and parser are the first step of a
Stitchwort parser for Stitchwort itself, and it would be easy to drift
into treating them as that.
*The change:* nothing beyond three cheap habits in the twin's parser (its
own namespace and gate, byte offsets kept, a result per declaration). No
lowering in Stitchwort and no work on calling Stitchwort code from the
compiler until stage 6 reports, and then only if native speed is within
about 2–3 times of Rust on the parser or a Stitchwort-written tool wants
the tree.
*What it should do:* keeps the option at no cost, and spends nothing on a
direction whose main obstacle (speed, with performance work paused) this
project will measure. **[rec: yes, door open, no plan]**

**Decided here as implementation** (say if you disagree): the parser builds
the tree directly, not through marks; no error recovery in the twin; the
rewrites are tree functions; the safety check compares lossless trees; the
batch stream for files; fuel for the parser, the rules and the engine; the
parser stage starts after recovery's S3 if the orchestrator can arrange it.

## Findings worth tickets

- **SW-3149 (native executables fail to start from the main checkout)
  still reproduces** today, and is this project's first prerequisite. It
  deserves a higher place than backlog once D3576 is yes.
- **SW-3147 (fmt's time is in comparing trees as text) is unchanged:** 86%
  of an 8.3 s run. With the lowering done, the fix can be to compare
  lossless trees, as §3.4 describes for the twin. The Rust formatter also
  parses each file five or more times (the refusal, the bracket and merge
  rewrites, the tree, the checks) where one tree would do.
- **A list of one bracketed range with a trailing comma is never
  formatted:** a declaration holding `[(0 ..< n),]` is left as written,
  with no message and exit 0 [measured; `[(n),]` is formatted], because
  the lowering reads that comma (`lower/exprs.rs`, `list`; it is how
  `W-RANGE-IN-BRACKETS` is kept quiet). Either the lowering stops reading
  the comma, or the formatter keeps it there.
- **`stitchwort fmt` is silent about declarations it leaves as written:**
  only `dev fmt-tree --verbose` says. A line on standard error would have
  shown the case above.
- **No text literals in patterns:** `| "def" => …` is `E-PARSE`, "expected
  a pattern or `=`" [measured]. A lexer's keyword table, and any program
  that reads commands, wants it. Worth a design ticket if there isn't one.
- **`Std.Parse` is fixed to `List Char`,** so it can't parse a token
  stream. Generalising its input is a design question for the library.
- **SW-3148 (large heaps slow in native code), new numbers:** lexing and
  parsing are linear to 5.3 MB; printing took 10 times as long on 5 times
  the input; about 500 bytes of heap per input byte; memory is reclaimed
  between passes. For the ticket.
- **SW-3150 (no file access, no cheap text slices): unchanged.** Still the
  reason for the batch stream.
- **`Option.getOr` doesn't exist** though `List.getOr` and `Array.getOr`
  do (`Option` has `getOrElse`) [measured]. A naming inconsistency.
- **`dev tree --print` has no trivia.** A token dump with comments and
  blank lines (stage 0 adds one) would also serve the Rust formatter's own
  tests.

## Appendix A: the probes

In the lane's scratchpad, run with `stitchwort run --native FILE -- MODE <
INPUT` (`build --native` executables don't start: SW-3149). Inputs: the 760
`.sw` files of std, `aoc/src` and `games` concatenated (5.3 MB), its first
million bytes, its first 200 KB, and the three largest files (498 KB).
Start-up (check and compile, on empty input) is 0.44–0.54 s and is
subtracted in §5.

- **Probe 1** (115 lines). `Token = { text, width, kind }`; `scan` is
  structural on `List Char` (words, single symbols, brackets);
  `build` folds the tokens into `Tree = Leaf | Group (children: List
  Tree)` with a stack of open brackets; `toDoc` and `docsOf` (defined
  together) turn it into `Doc = Txt | Line | Nest | Grp | Cat`; `layout` is
  the Wadler loop over a list of `{ indent, flat, doc }` with fuel, `fits`
  with fuel; the pieces are joined with `Text.joinWith` and written once.
  Mode `check` scans and builds the output again and compares the trees
  with derived `==`. It checked first time apart from the text patterns in
  `main`. On 1 MB: 251,591 tokens, 19,589 groups, 147,244 output lines,
  none over 120. The 5.3 MB run is not valid: brackets inside strings and
  comments leave groups open across files, so indentation grows without
  limit (286 MB of output, 51 s, 10.9 GB); the repeated 1 MB input stands
  in for it.
- **Probe 2** (100 lines). The same scanner, with a precedence on symbols;
  `atom`, `items`, `app`, `expr`, `operators` and `top`, mutually recursive
  on fuel, returning `(Tree, List Token)`; `Tree = Leaf | Node (kind)
  (children)`. Checked first time. 167,826 nodes on 1 MB, 991,950 on
  5.3 MB. Mode `same` parses twice and compares: 0.41 s on 1 MB, 3.26 s on
  5.3 MB.
- **Probe 3.** Probe 2 over `Array Token` and a position (`tokens.get
  pos`).
- **Probe 4.** Probe 1's `format` called N times on the same 200 KB in one
  process, summing the output lengths.
- **The Rust side.** `fmt --check` and `dev tree --time 3` over the four
  folders; `/usr/bin/sample` for 5 s on the `fmt --check` run; `dev
  fmt-tree` over std, `aoc/src` and `games`; `dev tree --print` on a
  one-line file; `fmt -` and `dev fmt-tree --verbose` on the one-item
  lists.

## Appendix B: the first plan (superseded)

*The plan of 13 November 2026 (SW-3145), as written, against the token-and-line
formatter that SW-3194 deleted. Kept as history. Its lexer design, its
totality table for index passes, its batch stream and its reasoning about
disturbed input still hold; its architecture, stages, parser scope and
questions are replaced by the sections above. Its claims were read or
measured at `341c69c9d`.*

### First plan: In plain words

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

### First plan: 1. Scope

#### What the Rust formatter does [source]

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

#### What it changes besides whitespace (the full list) [source]

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

#### In and out

**In:** all of the above, on every file of the `fmt_repo` list (1,695
files, 6.8 MB, 132,000 lines [measured]), which uses the whole surface
language. Widths and columns are counted in UTF-8 bytes, as the oracle
counts them (`∀` is 3), or the 120-column test will disagree.

**Out:** diagnostics that match the Rust ones (errors may differ, only
"refused or not" must agree); the LSP and playground hooks; range
formatting; the lexer's long explanations of invisible characters;
replacing `stitchwort fmt`.

### First plan: 2. Architecture

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

#### Totality

| Part | How it terminates |
|---|---|
| Lexer | structural on the character list |
| Declaration split, roles, bracket finding, line building, spacing | index passes with `decreasing size - k`; inner "pop while" loops are structural on the stack list |
| Indentation (`indents`) | the same; the sibling-group pass folds over a sorted list |
| Paren dropping (`loop { find a pair; drop it }`) | fuel: the number of parentheses |
| Parser | fuel: tokens left plus a margin |
| Printer | structural on the lines |

`main` is `{IO}` only. No `Partial` anywhere is a stage checkpoint.

### First plan: 3. Performance

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

### First plan: 4. Testing

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

### First plan: 5. Proofs (a later stage)

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

### First plan: 6. Stages

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

### First plan: 7. Questions for Matt

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

### First plan: Appendix A: the probes

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
