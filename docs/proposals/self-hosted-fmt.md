# A Stitchwort formatter written in Stitchwort

**Status:** third plan, 17 November 2026 (SW-3417), refreshing the second
(SW-3228, 14 November) with what the toy formatter has shown since. The
second plan's design was a *twin*: a port of the Rust formatter that checks
its own output at run time. Matt's decisions since (D3623, D3635, D3636)
replace that with a formatter that is *proved*: tidy passes, then a printer
that changes only white space, each proved, with no check when it runs.
[What changed (17 Nov 2026)](#what-changed-17-nov-2026) lists every change;
the second plan's text that no longer holds is gone from the body, and the
first plan is kept as history in
[Appendix B](#appendix-b-the-first-plan-superseded). Paper lane: nothing
was built or run for this refresh. It stops for Matt's decisions
([§10](#10-questions-for-matt)).

Claims are marked **[measured]** (run on Speedwell for this or an earlier
note, or counted from `git log` and the board; each says where),
**[source]** (read in the code at `82251a9b4`), **[estimated]** (my
reasoning, not tested) or **[assumed]** (taken as true without checking,
and said why). Times are **agent time** unless they say elapsed: the time
lanes spend working, summed. Past estimates here ran about three times high
(the median actual over 1,034 closed tasks was 0.33 of the estimate), and
the estimates below are made from the toy's actuals, not from scratch.

## What changed (17 Nov 2026)

| Second plan (14 Nov) | Now | Why |
|---|---|---|
| A twin, mirroring `crates/fmt` module for module | **Replaced.** Tidy passes (tree to tree), then a printer that chooses only white space ([§2](#2-the-design)) | D3623 (Matt, 16 Nov 2026: direction C of [after-the-toy-proof.md](after-the-toy-proof.md) §4.3); the Rust formatter was reshaped the same way (D3624; SW-3495, SW-3496, SW-3610) |
| A safety check at run time: parse the output, compare trees; theorems 1 and 2 hold "by validation" | **Replaced.** No check at run time, ever. The theorems are proved from the program's definitions ([§7](#7-proofs)) | Matt, 15 Nov 2026: "my ambition is that we don't need the runtime check because we have formally verified the behavior is correct"; D3620 ("no run-time check, ever"). The toy did it: SW-3418, merge `dcda74fb2` |
| "Same program" is "the same lossless tree, after erasing layout" | **Replaced.** Same `meaning`: the tree with exactly the formatter's freedoms forgotten, a definition in Stitchwort, cross-checked against the compiler's hashes by the fuzzer ([§3.4](#34-what-the-same-program-means)) | D3635, D3643 |
| §3.2: build the tree directly by hand (B); `Std.Parse` (C) ruled out because it reads only characters | **Reversed.** `Parse` now reads tokens, and the parser is written on it (C), so its proofs stand on std's parser-proof library ([§3.2](#32-the-options)) | `Parse` became generic over its input (the toy's parser runs on `Parse.Located Token`); SW-3414 still preferred hand-written for speed; D3636 (Matt, 16 Nov 2026: "let's plan to write it with standard parse") decided against it |
| An untyped tree: `Node (kind) (children)` | **Changed:** a tree typed per construct, as the toy's, with a dump in `dev tree --print`'s format for the gate ([§2](#2-the-design)) | proofs go by cases on constructors (after-the-toy-proof.md §4.3, risk i) |
| Declarations left as written when a check fails | **Gone.** There is no check to fail; every comment has a place | D3618, D3619; [§3.5](#35-refusals) |
| SW-3149 (built executables don't start) blocks stage 0 | **Done** (SW-3149, `d3d200a2f`) | [§5](#5-speed) |
| SW-3150 (no file access, no cheap text slices): use a batch stream on standard input | **Done** as `Files` (SW-3338) and constant-time `Text` slices (SW-3337); no batch stream | SW-3150 was superseded by SW-3234's design |
| Theorems: two cheap ones "by validation"; a direct proof "months, not recommended" | **Measured on the toy:** the direct proof took about 10 hours elapsed for 1,262 theorems (SW-3418); Toy++ T1–T3 added 348 in about 4 agent-hours ([§8](#8-stages)) | `git log --grep`, the tickets' notes |
| 42–59 lane hours to build; proofs "2–3 days, then open" | **Re-estimated** in agent time: about 15–25 hours to build, 40–70 to prove ([§8](#8-stages)) | the toy's actuals |
| D3617: keep the check, skip the re-parse on unchanged files | **Moot for this formatter** (it has no check); an ordinary speed change for the Rust one ([§7.6](#76-d3617)) | |
| D3576, D3577, D3578 | D3576 was replaced by D3579 (build the pieces, then a toy, then decide). D3577 and D3578 were never answered; D3577 comes back as Q3, D3578 stands as written ([§9](#9-towards-self-hosting-a-direction-not-a-plan)) | |

Decisions this plan rests on, all Matt's: D3558 (the formatter chooses
line breaks), D3618 and D3619 (every comment has a place; odd layouts for
odd comments are fine), D3620 (no run-time check), D3623 (passes, then a
white-space printer), D3624 (the Rust formatter takes the same shape),
D3625 and D3626 (Toy++ first, in place), D3635 and D3643 (`meaning`, the
same tree in plain form), D3636 (the parser on `Parse`), D3663 (the "must"
set of properties, for Toy++).

## In plain words

**The problem.** We want a demanding real program written in Stitchwort,
and a formatter is a good one. Matt's aim for it is more than a port: a
formatter whose correctness is *proved*, so it never needs to re-read its
own output to be safe. The toy formatter (Sprig, `tools/toyfmt`) showed
that this can be done, and Toy++ is now showing it for a formatter that
also changes tokens, as the real one does.

**The change.** A new project, `tools/fmt/`, in four parts:

1. *A lexer*, giving the same tokens and comments as the Rust one.
2. *A parser on std `Parse`*, giving a tree typed per construct; its dump
   must match the Rust parser's tree node for node.
3. *Tidy passes*, each a function from tree to tree: `∀` after a theorem's
   name, the comma before a closer dropped, spare brackets dropped,
   parameters of one type merged. Where a comment belongs is a reading
   rule (rule N) applied as tokens are read.
4. *A printer* that changes only white space: the layout engine and a rule
   per construct.

Then proofs, in layers, that formatting keeps the program's meaning, keeps
every comment, and changes nothing the second time, with no check when it
runs.

**What it should do.**

- Format the repo's files to the same bytes as `stitchwort fmt`, and
  refuse the same broken files.
- Take about 15–20 s for the 6.5 MB of the repo in one process
  [estimated from the toy's 2.05–2.2 s per MB with no check, measured in
  SW-3383 and SW-3414; Toy++ T7 measures the rate with passes]. The Rust
  formatter takes 8.3 s, of which about 1.1 s is real work [measured
  14 Nov, §5].
- Cost about 15–25 agent hours to build and 40–70 to prove [estimated,
  §8], in stages that each stand on their own.

**Self-hosting.** The lexer, typed tree and parser are what a Stitchwort
parser for Stitchwort itself would start from, now with proofs; still a
direction, not a plan
([§9](#9-towards-self-hosting-a-direction-not-a-plan)).

## 1. What is being matched

### The Rust formatter today [source]

The Rust formatter was reshaped into the architecture this plan copies
(D3624, [fmt-passes.md](fmt-passes.md)). For each file
(`crates/fmt/src/printer/mod.rs`, `format_tree_in`):

1. Lex with trivia, then apply rule N (`tidy.rs`): a trailing comment
   written on a comma, a closing bracket or a record update's `|` moves to
   the token before; a comma holds no comments; comments lose trailing
   spaces; a comment after `->` moves before it. It is applied to every
   token sequence the formatter reads, input and output alike.
2. Parse to the lossless tree; refuse the file on any error (D1021).
3. Four passes (`passes.rs`, `PASSES`): P1 `∀` after a theorem's name
   (D3472), P2 the comma before a closer dropped (D1012), P3 redundant
   round brackets dropped (D2307), P4 neighbouring parameters of one type
   merged (D3565). Each returns edits to the text, which is parsed again,
   so every intermediate is a real program.
4. Print: per declaration, the rule for each node gives a layout document
   (`rules.rs`), printed in 120 columns (`engine.rs`).
5. Check (`check_file`): the same tokens as the tidied text, the same
   comments, and the original's compiler tree up to the passes' changes
   (`same_program.rs`, SW-3610). A file that fails is `Error::Internal`
   and kept as it was.

So the Stitchwort formatter matches a formatter of the same shape, which
was the point of D3624: the passes, their order and rule N can be ported
one for one, and what differs is only that the Stitchwort passes work on
the tree, not the text, and that the check becomes proofs.

### Its size [source, lines outside tests, at `82251a9b4`]

| Part | Rust | The Stitchwort formatter's counterpart |
|---|---|---|
| Lexer (`crates/syntax`, `lexer.rs`) | about 1,535 | all of it, less the long explanations of invisible characters |
| Parser (`parser.rs`, `parser/`) | about 6,150, 234 functions | the grammar on `Parse`; not the wording of its errors, not recovery |
| Tree (`tree.rs`) | 866, 94 node kinds | a typed tree; the dump |
| Lowering (`lower.rs`, `lower/`) | about 4,000 | none, except its three errors ([§3.5](#35-refusals)) |
| Rule N (`tidy.rs`) | about 185 | all |
| Passes (`passes.rs`, `parens.rs`, `merge.rs`) | about 640 | all, as tree functions |
| Engine (`engine.rs`) | about 825 | all (it was 636 on 14 Nov; since then S39's closers before a waiting comment and SW-3447's `fits` after one) |
| Rules (`rules.rs`) | 2,096 | all |
| Spacing (`spacing.rs`) | 263 | all |
| Checks (`check.rs`, `same_program.rs`, part of `printer/mod.rs`) | about 600 | none: replaced by proofs |

About 12,500 lines of Rust to match, the lowering and the checks aside;
I'd expect 8,000–11,000 lines of Stitchwort program [estimated: the toy's
program is 1,680 lines for a grammar about a fifth the size], and many
times that in proof.

### In and out

**In:** the same bytes as `stitchwort fmt` for every file it formats; the
same refusals for lexical and syntax errors and the lowering's three
errors; the "must" properties of
[formatter-properties.md](formatter-properties.md) §4, proved
([§7](#7-proofs)).

**Out:** diagnostics that match the Rust ones (only "refused or not" must
agree); error recovery ([§3.3](#33-error-recovery-s1-to-s5)); the LSP and
playground hooks; replacing `stitchwort fmt` (Q3).

## 2. The design

```
lex → rule N (settle) → parse  →  P1 → P2 → P3 → P4  →  print
       (reading rule)              (tree to tree)        (white space only)
```

| Module (namespace) | What | Rust counterpart |
|---|---|---|
| `Syntax.Token`, `Syntax.Lexer` | token kinds; the lexer with trivia, over `Text` slices | `lexer.rs` |
| `Syntax.Settle` | rule N on the lexer's tokens | `tidy.rs` |
| `Syntax.Tree` | the typed tree (a type per construct family: declarations, headers, expressions, patterns, types, blocks), each token's comments in its own slot; a dump in `dev tree --print`'s format | `tree.rs` |
| `Syntax.Parser` | the grammar on `Parse` over located tokens, layout as a parameter, as the toy's | `parser.rs`, `parser/` |
| `Fmt.Meaning` | `meaning`: the tree in plain form ([§3.4](#34-what-the-same-program-means)) | `same_program.rs`, in spirit |
| `Fmt.Passes` | P1–P4, on one shared traversal | `passes.rs`, `parens.rs`, `merge.rs` |
| `Std.Doc` (or `Fmt.Doc`) | the layout document and engine, with its theory | `engine.rs` |
| `Fmt.Spacing`, `Fmt.Rules` | the space-or-not table; the rule per construct | `spacing.rs`, `rules.rs` |
| `Fmt.Format`, `main` | the file driver over `Files` | `printer/mod.rs`, the CLI |
| `*.Proofs` beside each | the layers of [§7](#7-proofs) | none |

Choices, and why:

- **A typed tree, not `Node (kind) (children)`.** Every layer of the toy's
  proof goes by cases on constructors, and the passes' side conditions
  (what may stand where a bracket pair stood) are about specific
  constructs. A generic node with 94 kinds would push every case into a
  kind test and a list shape. The cost is that the tree dump is a
  function written per type, not one generic walk.
- **The parser on `Parse`** (D3636; [§3.2](#32-the-options)).
- **Passes on the tree, on one traversal.** Toy++ T0 found that one
  `Expr.walk` type-checks and carries all four passes (SW-3600,
  `tools/toyfmt/plus/SKETCH-PLUS.md`); Toy++ T5 measures whether its
  lemmas hold up. At 94 kinds this is the difference between a pass
  costing a few dozen theorems and one costing an induction over every
  construct.
- **Rule N as a reading rule, not a pass.** Plain text can't hold its
  result, so it must run every time tokens are read, as in Rust and in
  Toy++ T3 (SW-3675, SW-3676).
- **The engine knows closers.** A `Closing` leaf for `)`, `]` and `,`,
  written before a waiting trailing comment and measured that way, so
  `[a, b] -- c` prints when it fits (S39). Toy++ T3a added it with its
  theory (SW-3675). See [§3.6](#36-what-toy-adds-that-the-real-formatter-needs).
- **The parser's modes are arguments**, as the toy's layout parameter is.
- **No `Partial`, no fuel the proofs can't see.** [§4](#4-totality-and-termination).

**Where it lives and how it runs.** `tools/fmt/`, a project with its own
`stitchwort.yaml`, built with `stitchwort build --native tools/fmt` to one
executable that reads and writes files through `Files`, as the toy's
driver does (SW-3342). The project's own files join the repo's formatted
set, and the formatter formatting its own source is a named test.

## 3. Parsing

### 3.1 What the Rust parser does [source]

The Rust parser cuts a file into declarations at column 0, parses each,
and records *marks* that a builder nests into the lossless tree
([parser-end-state.md](parser-end-state.md), strict marks since SW-3280).
Marks fit Rust; none of their reasons apply here. The Stitchwort parser
returns values.

### 3.2 The options

| | How | For | Against |
|---|---|---|---|
| A. Mirror the marks | thread a list of marks; nest them afterwards | line for line like the Rust code | machinery whose reasons are gone; nothing to prove things about until the end |
| B. Hand-written, building the tree directly | each function takes modes, the token array and a position, returns the node and the new position | fastest: the probes lexed at 0.11 s/MB and parsed a small grammar at 0.06–0.13 s/MB more [measured, 14 Nov]; follows the Rust parser function for function | **no proof library**: every read-back and walk lemma would be built from nothing |
| **C. `Std.Parse` over tokens (decided, D3636)** | combinators over `Parse.Located Token`, layout as a parameter, as the toy's parser | std's parser-proof library: `Reads`, `ReadsIn`, `Gives`, the declines toolkit (Parse proofs L1–L5, SW-3503 to SW-3507, all done); every one of the toy's parser theorems stands on it | 7–10 times slower than B's probes [measured on toy grammars, SW-3414 report §3]; not function for function with the Rust parser |
| D. Generated, table-driven | a grammar file and a generator | none here | no grammar file; columns decide where blocks end |

**What SW-3414 found, and why it was overruled.** The toy's final report
(`docs/reviews/SW-3414-toy-formatter-report.md`, §3.2) recommended keeping
B: the twin needed nothing `Parse` gives (it refused rather than reported,
and had to follow the Rust parser to pass the tree-dump gate), and the
safety check paid `Parse`'s cost twice. Both halves changed with the
proof. Every one of the toy's parser theorems (336 on 16 Nov,
after-the-toy-proof.md §4.6) rests on `Parse`'s
library, which a hand-written parser would have to rebuild; and with no
check there is no second parse, so the toy formats at 2.05–2.2 s per MB
[measured, SW-3383 and SW-3414], inside the target at the real
formatter's size [estimated, §5]. D3636 chose C, with a timing in Toy++
T7 to confirm before stage 2.

**What C gives up.** Following the Rust parser function for function. The
gate makes up for it: the tree dump must match the Rust parser's on every
file, whatever the internal structure.

**The gate.** `stitchwort dev tree --print` prints a file's lossless tree
as indented text [measured, 14 Nov]. The Stitchwort parser prints its
typed tree in the same format, and the two dumps must be identical for
every file in the repo (513,260 nodes in 27,583 declarations on 14 Nov
[measured]).

**Termination.** `Parse`'s recursive combinators carry their own fuel
(`recursiveWith`), and the toy's read-back proofs work through it
(`runsRecursiveWith`, `runsRecursiveWithFact` from L5).

### 3.3 Error recovery (S1 to S5)

Unchanged from the second plan. The formatter refuses a file with any
syntax error (D1021), so its parser is strict: it stops at the first
error, and `Error` and `Gap` nodes never reach the passes or the printer.
Recovery never makes a broken file acceptable, so the tree dump of
correct files is unaffected. A parser for the compiler itself would need
recovery; that is [§9](#9-towards-self-hosting-a-direction-not-a-plan)'s
concern.

### 3.4 What "the same program" means

**The intended meaning** is the Rust formatter's: the output lowers to the
same compiler's tree as the input (`same_program.rs`, up to one binder per
name). A Stitchwort proof can't say that: the lowering is 4,000 lines of
Rust.

**Why not the lossless tree.** The formatter changes the lossless tree on
purpose: brackets dropped, commas dropped, parameter groups merged, `∀`
added, comments moved across closers. "The same lossless tree" is false
of every file those touch.

**What is proved instead (D3635, D3643).** `meaning`, a function in
Stitchwort: the typed tree in *plain form*, each freedom set to one
spelling, wrapped in a `Meaning` type so a plain tree can't be printed by
mistake:

| Freedom | In plain form |
|---|---|
| A redundant bracket pair (expression or type) | forgotten, if it holds no comment: the tree's shape already says how the expression groups |
| Parameter grouping, `(a b: Nat)` against `(a: Nat) (b: Nat)` | split to one binder per name |
| `∀` after a theorem's name | present, with no comments |
| A comma before a closer | the flag set to absent |
| Which side of a closer a comment was written | nothing to do: rule N already put it on its token |
| Blank-line counts | present or absent, as the tree keeps them |
| A text block's lines | by value |

Everything else is kept: names, literals, operators, order, every
comment's text and its token. So the theorem chain is: the parser reads
the source to a tree; each pass keeps `meaning`; the printer is exact
(`parse (print t) = t` for a tidy tree). Between the tidied tree and the
output, the lossless tree *is* the same; between the source and the
output, `meaning` is.

**The gap, and what covers it.** `meaning` is a definition we trust, not a
theorem: if it forgot something the compiler reads, every pass theorem
would still go through. Two things cover that:

- the fuzzer's comparison of the compiler's hashes before and after
  formatting (D3635's cross-check), kept for as long as the lowering is in
  Rust; and
- an Opus review of `meaning` case by case when it is written (D3643 for
  Toy++; the same here).

One known case shows why the cross-check matters: the lowering once read
the comma in `[(0 ..< n),]` (SW-3229, fixed 14 Nov in `lower/exprs.rs`).
Had `meaning` been written then, it would have forgotten a comma the
compiler saw.

**What it costs** [estimated]:

- `meaning` itself: about 60 lines for Sprig (toy-plus-plus.md §2); for
  94 node kinds on the shared traversal, most kinds are the identity, and
  I'd expect 200–400 lines, of which the trusted substance is the seven
  rows above.
- Per pass, three theorems (keeps `meaning`, idempotent, keeps what the
  parser and the earlier passes guarantee), each an instance of the
  traversal's lemmas if T5's experiment holds: 300–600 theorems for the
  four passes at the real size. Without the shared traversal, nearer
  passes × theorems × node kinds, which after-the-toy-proof.md §7 put at
  several thousand.
- A permanent dependency on the fuzzer's hash comparison, until the
  lowering is itself in Stitchwort (D3635: revisited only if the compiler
  moves).

### 3.5 Refusals

The lowering raises three errors of its own [source, 14 Nov]: a parameter
named twice in a header, an or-pattern that binds names, and a condition
on an arm with `()` and no body. The formatter ports them as one small
check on the tree, so it refuses the same files. The gate is the 1,157
deliberately unformatted files under `examples` [measured, 14 Nov], file
by file. "Left as written" is gone: with no check there is nothing to fall
back from, and since D3618 every comment has a place.

### 3.6 What Toy++ adds that the real formatter needs

Toy++ ([toy-plus-plus.md](toy-plus-plus.md)) rehearses each kind of token
change on Sprig. Its status, and what each part hands the real formatter:

| Toy++ part | Status | For the real formatter |
|---|---|---|
| T1–T1c: `printParses` over predicates; `formatKeepsComments`, `formatSameTree`, refusals, `Degenerate.sw` | done (SW-3624, SW-3632, SW-3641) | the "must" set's statements (D3663); the comment-carry walk cost 1.7 lemmas and about 29 lines per parser function [measured, SW-3641] |
| T2: typed parameter groups, `takes`, type brackets | done (SW-3666, SW-3667, merge `b00c0b7be`) | how a second bracket kind and grouped binders enter every layer |
| T3: **rule N**: `settle` on tokens; the engine's `Closing` leaf and its theory; commas hold no comments; `Settled`; `settledViews` | done (SW-3675, SW-3676, merges `359d1f8fc`, `36277b392`); review SW-3677 running | the hardest part of the printer's proof. Two lessons: `printedTokens` lost its "pieces in order" clause (rule N makes it false; `printedEvents` keeps the exact order), and `Settled` is pairwise, since `Tidy` is false of settled tokens (SW-3675's note) |
| T4: `meaning`, `tidy`, `format`; P1 (`takes`) and P2 (**trailing commas**: the parser accepts them, with a flag, and the pass drops them) | next | the pass frame and the first two passes |
| T5: P3 (spare brackets, the precedence side condition) and the shared traversal | after T4 | whether passes are cheap at 94 kinds |
| T6: P4 (merging) and the P3-before-P4 order | after T5 | the one real ordering dependency |
| T7: the timing (D3636), the disturber's new changes, counts by layer, `toy-v2` | last | the bar before this plan's stage 2: at most 3.0 s/MB with passes and rule N, no check |

**Two engine findings the real engine must take in**, both in the toy's
backlog:

- **SW-3452: `fits` measures from the new line after a trailing
  comment.** The Rust engine does (SW-3447); the toy's doesn't, which
  gives odd layouts (s05, s06, s08, s11, s17, s19 of the comment probes)
  and a call whose `)` sits left of its argument. Since the output must
  match Rust byte for byte, the Stitchwort engine needs it, and `fits`
  then takes the indent and width, so the engine's budget proofs
  (`printBudgetEnough`) change. Best done once, in the toy, before the
  engine moves to `Std.Doc`.
- **SW-3416: `Doc.group` recomputes `forcesBreak` over its whole inner
  document**, which is quadratic in nesting. Harmless at the toy's sizes;
  the real rules nest deeper, so the node should cache it. The cached
  field becomes an invariant the engine's theory must carry ("the cache
  equals the computation").

**Rule N at the real size.** The Rust rule N has four clauses (`tidy.rs`)
where Sprig's has two: it also moves a comment off a record update's `|`
and from after `->` to before it. Each is a new case in `settle` and in
`Settled`, not a new idea. The Rust rule N also had a bug Toy++ found:
it dropped a comment when two landed on one token (SW-3606, fixed).

## 4. Totality and termination

| Part | How it terminates |
|---|---|
| Lexer | structural on the input, or a measure on the position in the `Text` |
| Rule N | structural on the token list |
| Parser | `Parse`'s own fuel (`recursiveWith`), which its proof library handles |
| Tree dump, `meaning`, passes, the three lowering errors | structural on the tree, through the shared traversal |
| Rules | structural; the toy's rules are, and the rules' proofs need it |
| Engine | the toy's budget (`3*size+3` steps is enough, `printBudgetEnough`); SW-3452 changes its proof |
| `main` | `{IO, Files}` only |

No `Partial` anywhere is a gate of every stage.

## 5. Speed

**The Rust side [measured, 14 Nov].** `stitchwort fmt --check` over std,
`aoc/src`, `games` and `examples` (1,461 files, 6.5 MB): 8.3 s, of which
86% was comparing compiler's trees as text (SW-3147, still in the
backlog); the real work is about 1.1 s. Not re-measured since the passes
landed: each pass now parses the file again when it has edits
(`passes.rs`, `run`), which adds to the real work on files that change and
nothing on files that don't [source].

**The toy [measured].** With no check, the toy formats 933 KB in 1.91 s,
2.05 s/MB, at load 3.5 (NOTES.md "Speed (SW-3383)"); 2.2 s/MB in SW-3414's
report. With the old check it was 4.3 s/MB. Not re-measured since the
direct proof (SW-3418 added helper calls to the lexer and parser) or rule
N (`settle`): Toy++ T7 does that.

**Estimate.** At the toy's rate, 6.5 MB is about 14 s. The real grammar
has about four times the toy's parser functions, but the rate per byte
depends on how many `Parse` operations each token costs, which is
grammar depth, not grammar size. I'd plan on 2.5–3.5 s/MB, **15–23 s for
the repo** [estimated]. The second plan's 1.8–3.9 s/MB assumed a
hand-written parser and a check; this drops the check and pays for
`Parse`.

**Target (unchanged):** all of the repo in one process in under 30 s on
Speedwell, aiming at 20 s; peak memory under 500 MB. Toy++ T7's bar
(3.0 s/MB) is set from it. If the real parser misses, the work is `Parse`
speed (operations in place, D3430), which D3636 made
formatter work too.

### What in Stitchwort was missing, and is now

| | 14 Nov | Now |
|---|---|---|
| SW-3149 (built executables don't start) | failed | **done** (`d3d200a2f`: the CLI builds its runtime library and checks its marker) |
| SW-3150 (no file access; no cheap text slices) | unchanged | **done** by SW-3234's design: `Files` (SW-3338), constant-time `Text` slices (SW-3337). `Files.walk` is still to come (SW-3415, backlog); the toy has its own |
| `Std.Parse` reads characters only | ruled out C | generic over its input; the toy's parser runs on tokens |
| No text patterns | a `Map` or `==` chain for keywords | text patterns, stages 1 and 2 (SW-3284, SW-3288) |
| SW-3148 (large heaps slow in native code) | milder, still there | unchanged (backlog); one file at a time avoids it |
| SW-3147 (fmt compares trees as text) | 86% of fmt's time | unchanged (backlog, parked with speed work); only the Rust formatter pays it |
| Check time for a large project with a 234-function parser | unknown | still unknown; the toy's check time at 1,491 theorems is not recorded as one figure (T7 records it) |

## 6. The comparison harness

One command, `task fmt:twin`, with a stage argument: it builds the native
executable, runs it over a list of files, and compares with what the Rust
side gives, printing counts and the first difference. The Rust side's
answers are cached outside the repo, keyed by the input's hash and the
hash of `crates/syntax` and `crates/fmt`.

| Compared | Rust side | For |
|---|---|---|
| Tokens with trivia after rule N, one line a token | a new `dev` dump | stage 1 |
| The lossless tree | `dev tree --print`, exists | stage 2 |
| Refused or not | `fmt --check`'s exit and message | stages 2 and 5 |
| The tidied tree's dump, pass by pass | a `dev` dump after `passes::run` | stage 4 |
| The formatted text | `dev fmt-tree --print`, exists | stages 5 and 6 |

**Inputs**, unchanged from the second plan: the golden pairs
(`crates/fmt/tests/it/golden`); the repo as it is (the fixed point); the
repo as it was before the reformat (the parent of `39de3aa7d`, 6 MB of
author-laid-out input); the formatter fuzzer's programs, written out from
a seed; and a disturber, at run time from a seed. Add the comment probes
and the Toy++ fuzz inputs (`tools/toyfmt/plus/inputs/`), translated.
Nothing new is committed beyond the harness.

**This is a test, not a run-time check.** The harness compares the
program with the Rust formatter while it is built; the formatter itself
answers without reading its output back. Once the proofs are done, the
harness still has one job the proofs can't do: show that the Stitchwort
formatter's *style* is the Rust one's.

**Lanes and the budget.** A lane runs the goldens and a handful of named
files (seconds). The full run is a broader suite: the verifier runs it
after a merge that touches `tools/fmt`, `crates/fmt` or `crates/syntax`,
and Overmind in its rolling check.

## 7. Proofs

### 7.1 What the toy proved, measured

The toy's top theorems (`tools/toyfmt/src/Toy/Fmt/DirectProofs.sw`), with
no open goals and no axioms, and the driver formatting with no re-parse
(merge `dcda74fb2`; the checked `format` deleted in SW-3484):

- `printParses`: a tree the parser produces prints, at every width, to
  text that parses back to that tree (over predicates since T1: `Parsed
  file`, not a source);
- `formatRoundTrip`, `formatIdempotent`, `formatAnswers` (named
  `formatDirect…` until SW-3484);
- since Toy++ T1b and T1c: `formatKeepsComments`, `formatSameTree`,
  `formatRefuses`, `formatRefusesOnly`, and `Degenerate.sw`'s three
  refuted silly formatters (SW-3632, SW-3641).

| | Theorems | Time | Source |
|---|---|---|---|
| SW-3418, the direct proof | 1,262 | 15 Nov 14:35 to 16 Nov 00:30, about 10 h elapsed, 148 commits, 18 parts | `git log --grep SW-3418` |
| SW-3490, the tidy-up | 1,262 → 1,143 | | merge `989a8cef0` |
| Toy++ T0 (sketch), Fable | 56 stated in a side project | 21 min (est. 75) | SW-3600 |
| T1, Sonnet | restated | 4 min (est. 15) | SW-3624 |
| T1b, Fable | about 38 (audited in its new namespaces) | 28 min (est. 45) | SW-3632 |
| T1c, Fable | 129 | 35 min (est. 120) | SW-3641 |
| T2a + T2b, Opus | about 55 (planned 100) | 25 + 21 min (est. 2 × 70) | SW-3666, SW-3667 |
| T3a + T3b, Fable | 70 + 174 = 244 (planned 100) | 40 + 82 min (est. 2 × 90) | SW-3675, SW-3676 |
| **Toy now** | **1,491** | | `grep -c '^theorem'` over `tools/toyfmt/src` [measured, `82251a9b4`] |

What that says, for estimating [measured from the rows above]:

- **Rate:** Toy++ T1–T3 added a net 348 theorems (1,143 to 1,491) in
  about 235 lane minutes, about 90 an hour. Net: the parser-proof library
  lanes (SW-3504, SW-3506) also removed toy theorems in that window, so
  the gross rate was a little higher. SW-3418 ran at a similar pace (about 80 a lane, lanes
  of 25–50 minutes, after-the-toy-proof.md §1).
- **Time estimates ran high:** Toy++'s eight lanes took 256 minutes
  against 575 estimated (0.45).
- **Theorem counts were not:** T2 came in at half its count, T3 at 2.4
  times. Rule N, the least certain stage, was the one that ran over.
- **The sketch is what makes estimates hold.** SW-3418's "lemmas left"
  stayed at "two to three lanes" for ten parts running until the rest was
  stated top-down with open goals (D3620); after that, 200–250 estimated,
  about 230 proved. Toy++ began with a sketch (T0) and has kept to its
  stages.

### 7.2 The theorems for the real formatter

The toy's statements, at the real size (sketch: names not settled):

```stitchwort
theorem printParses ∀ (file: SourceFile) (width: Nat) (parsed: Parsed file) (tidy: Tidy file):
    parse (file.print width) = Ok file

theorem formatKeepsMeaning ∀ (source output: Text) (h: format source = Formatted output):
    ∃ (before after: SourceFile) =>
      parse source = Ok before ∧ parse output = Ok after ∧ after.meaning = before.meaning

theorem formatIdempotent ∀ (source output: Text) (h: format source = Formatted output):
    format output = Formatted output

theorem formatKeepsComments ∀ (source output: Text) (h: format source = Formatted output):
    (lex output).comments = (lex source).comments
```

plus the rest of D3663's must set (`formatSameTree`, the refusals,
`Degenerate`), and per pass the three theorems of
toy-plus-plus.md §3.2. "Every comment kept" is stated between the two
texts through the lexer only, so it doesn't lean on `meaning`.

Not proved, and why:

- that the output is the Rust formatter's: that is the harness's job (a
  style is a choice, not a property);
- that `meaning` agrees with the compiler's tree: the fuzzer's hash
  comparison ([§3.4](#34-what-the-same-program-means));
- the "worth considering" properties of formatter-properties.md §4 (code
  tokens kept between texts, blank lines at text level): decided after
  Toy++ T6 (D3663).

### 7.3 Size, by layer [estimated]

From the toy's layers after Toy++ T3, scaled by what each layer grows with.
The toy figures are after the tidy-up and the parser-proof library (the
three walks are one walk since L4, SW-3506), so the library's saving is
already in them.

| Layer | Toy after T3, by layer [estimated: after-the-toy-proof.md §1's counts, less the tidy-up, plus Toy++'s additions; total measured] | Grows with | Real (94 kinds, 234 functions) |
|---|---|---|---|
| Engine, with `Closing`, SW-3452 and SW-3416 | about 300 | one engine, about 1.5× the code | 350–500, or about 100 new once it is `Std.Doc` |
| Lexer and rule N's token theorems | about 250 | lexer size (text blocks, interpolation, 4 clauses of N) | 500–900 |
| The parser keeps P (one joint walk) and carries comments | about 250 | parser functions × walk | 600–1,000 |
| Read-back | about 150 | parser functions or node kinds | 500–750 |
| Rules: words, joins, events, places, `Settled` | about 400 | rule functions (73 against 33; 7× the lines) | 900–2,000 |
| Spelling | about 120 | node kinds | 500–650 |
| `meaning` and passes | (T4–T6: about 150 estimated) | passes, with the shared traversal | 300–600 |
| Glue and the must set | about 50 | constant | 60–100 |
| **All** | **about 1,650 when Toy++ ends** | | **about 3,700–6,500, middle 5,000** |

Very low confidence at the top: the rules layer's spread is a factor of
two, and the T3 lesson (rule N ran at 2.4 times its count) says the least
certain layer runs over. A sketch stage (stage 3 below) replaces this
table with counts of stated theorems before the proof lanes start.

**Time.** At 80–110 theorems an agent hour, 3,700–6,500 theorems is
**about 40–70 agent hours** of proof lanes [estimated]. The second plan's
"not recommended: months" and SW-3418 part 1's "2–4 months for the real
formatter" were both made before the toy's proof ran. Part 1 estimated
2–4 weeks for the rest of the toy; it took about 9 hours elapsed.

### 7.4 What makes it cheaper

- **The shared traversal** (Toy++ T5): the largest single uncertainty in
  the pass layer.
- **`simp`** (simp-revisited.md): estimated at 22–29% of proof text on the
  engine slice; the passes are its best case.
- **`Std.Doc`**: the engine and its theory moved to std after Toy++
  (after-the-toy-proof.md roadmap step 5), so the real engine is a
  dependency, not a layer.
- **Proving the rules last.** The rules change weekly (the printer had 18
  commits in two days on 14 Nov). Their layer is the largest and the one
  every style change touches, so it is proved after the style settles, on
  the stage-6 program.

### 7.5 What a style change costs once proved

A change to a rule changes that rule's words, joins and events lemmas, and
the spelling of its construct; it never touches the passes, `meaning`, the
parser's walks or the engine. A new pass costs its three theorems and its
"keeps the earlier passes" lemmas. This is the price of "no run-time
check": every style change is also a proof change. It is why the rules
layer goes last, and why Q3 asks how the two formatters stay in step.

### 7.6 D3617

D3617 asked: keep the formatter's run-time check always on, and skip the
re-parse only when the output is the input's text
(`docs/reviews/SW-3414-toy-formatter-report.md`). It has been on hold
behind this plan. What the plan implies:

- **For the Stitchwort formatter: drop it.** There is no run-time check
  to skip. The toy already formats with none (SW-3418, SW-3484).
- **For the Rust formatter, until it is replaced: keep it, as an ordinary
  speed change.** The Rust formatter keeps its check (it has no proofs),
  and on an already formatted file the check compares the file with
  itself. Skipping it then changes no result, message or file on disk:
  the output *is* the input, a program that was accepted as written. So
  it falls under D3447 (optimisations that change no result are the
  orchestrator's call), with a performance-log entry, and needs no
  decision from Matt. It is most of `fmt --check`'s time on a formatted
  repo (86% is the check, §5) [estimated: the check is skipped for every
  file `--check` passes]. It is scheduled on its merits, with
  SW-3147.

## 8. Stages

Times are agent time [estimated from the toy's actuals: the toy's build,
stages A–D, took about 1.9 h against 15.5 h estimated (SW-3414 report),
and Toy++ ran at 0.45 of its estimates]. Each stage ends with its harness
count, its speed numbers, and friction notes in `tools/fmt/NOTES.md`.

| Stage | What | Gate | Model | Time |
|---|---|---|---|---|
| 0 | The harness: the token dump on the Rust side, cached Rust answers, the old-layout checkout, the fuzzer's programs written out, the disturber. Toy++ T7's timing has passed (D3636) | a stub that copies its input scores 0 of N on unformatted input and N of N on the repo | Sonnet | 1–2 h |
| 1 | The project skeleton; the typed tree and its dump; the lexer; rule N on tokens | token dump (after N) identical on every file that lexes; the same lexical refusals | Opus (sets the project's shape) | 2–3 h |
| 2 | The parser on `Parse`, in three lanes: expressions and patterns; declarations, headers and types; blocks, `match`, handlers and proofs. The lowering's three errors. A timing | tree dump identical on every file that parses; refused or not identical on every file; the parse rate per MB recorded against §5 | Opus for the first lane, Sonnet after | 4–6 h |
| 3 | **The sketch** (as SKETCH.md and Toy++ T0): `meaning` for 94 kinds; every top theorem and every layer's statements, in a side project with open goals, checked for fit; a count of stated theorems per layer | the side project checks with only open goals; §7.3 replaced by counts | Fable | 1–2 h |
| 4 | `meaning` and the four passes, on the shared traversal | the tidied tree's dump identical to the Rust passes' on every file | Sonnet, Opus for `meaning` and its review | 2–3 h |
| 5 | The engine (from the toy's, with SW-3452 and SW-3416, or `Std.Doc` if it exists), spacing, the file driver, the rules for declarations, headers, bodies and blocks | engine tests pass; every declaration using only those constructs identical | Opus | 2–4 h |
| 6 | The remaining rules, two lanes | identical on everything: goldens, old layout, fuzzer, disturbed; formats its own source | Sonnet; one rule family a fair DeepSeek trial | 3–5 h |
| 7 | Speed pass from profiles; the friction report | under 30 s for the repo | Sonnet, Opus for the report | 1–2 h |
| 8 | **Proofs**, in the order engine, lexer and rule N, parser (walk, carry, read-back), passes, rules and spelling, glue. Lanes on different layers run side by side | each layer's statements from stage 3 proved; `task audit:touched` clean; the must set with no open goals | Fable for the hard inductions and rule N, Opus, Sonnet for the mechanical layers | 40–70 h |

**Stages 0–7: about 16–27 agent hours** to a formatter that matches the
Rust one byte for byte and is fast enough, unproved. **Stage 8: about
40–70.** Stages 1–2 and 5 can run side by side; stage 3 needs the tree
from stage 1 and runs beside stage 2; stage 8's layers can start as soon
as their program and their stage-3 statements exist (the engine and lexer
early, the rules last). In elapsed time, with two or three lanes at once,
I'd expect stages 0–7 in about two days and stage 8 in one to two weeks
[estimated], usage allowing.

**What stands on its own.** After stage 2: a Stitchwort parser of
Stitchwort, on `Parse`, tested node for node. After stage 7: a second,
fast-enough formatter, and most of what there is to learn about the
language from writing it. After each layer of stage 8: that layer's
guarantee.

**Risks.**

- *The rules layer.* Largest, least certain, and moving. Proving it last
  limits churn; it may still be where the estimate is wrong.
- *`Parse` speed.* If stage 2's rate misses §5, the fix is `Parse` work
  that would then be scheduled. Toy++ T7 gives the first warning.
- *The target moves.* Every change to the Rust formatter or parser needs
  the Stitchwort one caught up, and after stage 8, its proofs too (Q3).
- *Check time* for a project of 5,000 theorems is unmeasured; the toy's at
  1,491 is to be recorded in T7.
- *`meaning` is trusted* (§3.4); the fuzzer's hash comparison must stay.

## 9. Towards self-hosting: a direction, not a plan

The second plan's section stands, with three updates:

- The parser is now on `Parse`, with proofs that it reads back what
  spells a tree. That is exactly "proofs about the parser that we want",
  which the second plan named as one of the two reasons a Stitchwort
  parser might be worth having.
- Speed is still the obstacle: every `check` parses all of std (69 ms in
  Rust [measured, lowering note]), and a `Parse` parser at 10–20 times
  that would add a second or more.
- The compiler's parser needs the Rust parser's messages and recovery;
  the formatter needs neither, so this project still doesn't show how
  hard that is.

D3578's recommendation stands (keep the door open, plan nothing more).

## 10. Questions for Matt

Three. The orchestrator numbers them.

**Q1. Start building stages 0–2 (harness, typed tree, lexer, parser on
`Parse`) once Toy++ T7's timing passes?** [rec: yes]
*The problem:* the parser is the largest part of the program and gates
everything after it; Toy++ can't tell us how the real grammar fares on
`Parse`.
*The change:* stages 0–2, about 7–11 agent hours [estimated], starting
after T7 records the toy's rate with passes (D3636's condition). Stage 1
can start beside Toy++ T4–T6, since the lexer doesn't depend on them.
*What it should do:* a parser of Stitchwort in Stitchwort, tested node for
node against the Rust one, and the first real measure of `Parse` at the
real grammar's size, before any proof work is committed.

**Q2. Is D3663's "must" set the real formatter's proof surface too?**
[rec: yes]
*The problem:* D3663 set the must set for Toy++ only. The three original
theorems admit a formatter that loses every comment or returns its input,
and the real formatter has had both kinds of bug (SW-3606).
*The change:* the real formatter proves the same set: round trip, same
meaning, idempotence, every comment kept, same tree gives same output,
refusals, and the degenerate examples.
*What it should do:* about 100–200 theorems over the three alone
[estimated from Toy++ T1b and T1c, 167 at the toy's size, much of it the
carry walk]; every observed failure class covered by a theorem.

**Q3. Two formatters until one is retired: how do they stay in step?**
(D3577, restated.) [rec: no merge gate; the Stitchwort formatter follows
in batches; decide on replacing `stitchwort fmt` after stage 7]
*The problem:* the Rust formatter changes most days, and once the
Stitchwort one is proved, every style change is also a proof change
(§7.5).
*The change:* no gate on Rust formatter lanes. The harness runs in
Overmind's rolling check and reports drift; the Stitchwort formatter is
caught up, with its proofs, in batches. After stage 7's numbers, decide
whether it replaces `stitchwort fmt`, which would end the double cost.
*What it should do:* the Rust formatter keeps its pace; the drift count
measures what a second implementation costs; replacing is decided on
speed and drift, not now.

**Decided here as implementation** (say if you disagree): a typed tree
with a dump in the Rust format; passes on one shared traversal; rule N as
a reading rule; no error recovery; rules proved last; the toy's engine
fixes (SW-3452, SW-3416) before the engine is reused; D3617 dropped for
this formatter and an optimisation (D3447) for the Rust one.

## Findings worth tickets

- **D3617 for the Rust formatter** (§7.6): skip the check when the output
  equals the input. An optimisation under D3447, scheduled on its merits
  (SW-3721).
- **The Rust passes parse again after each pass with edits**
  (`passes.rs`, `run`). Nothing measured; it adds to the 1.1 s of real
  work only on files that change. A tree-to-tree pass, as planned here,
  would not. Worth a line in SW-3147 when speed work resumes.
- **`fmt --check` has not been timed since the passes and the new check
  (SW-3610) landed.** The 8.3 s figure is from 14 Nov. A verifier or
  Overmind job could re-measure it in one run.
- **SW-3452 and SW-3416 are in the backlog but are prerequisites** for
  reusing the toy's engine here (§3.6); they should run before the engine
  moves to `Std.Doc`.
- Still open from the second plan: SW-3147 (comparing trees as text),
  SW-3148 (large heaps), `Files.walk` (SW-3415).

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
