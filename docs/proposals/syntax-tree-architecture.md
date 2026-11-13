# Syntax trees: one lossless tree, the compiler's tree, and who reads which

**Status:** discussion and recommendation, 13 November 2026 (SW-3155, context
for D3559). Paper lane: nothing is built. It stops for Matt's decisions
([§6](#6-questions-for-matt)).

Claims are marked **[source]** (read in the code at `6b506f328`),
**[measured]** (one probe with the release binary, [Appendix A](#appendix-a-the-probe)),
**[estimated]**, or **[from memory]** (how other tools work: not rechecked
against their sources for this note).

## In plain words

**The problem.** Stitchwort has one syntax tree, built for the compiler. It
throws away what the compiler doesn't need: comments, most brackets, how a
`let (a, b) = e` or a `lo ≤ x ≤ hi` was written. The new formatter (D3558
yes) needs all of that back, and so, more and more, do the editor's quick
fixes and the sweeps, which today scan text and tokens by hand. The
question is which tree should be the real one.

**Two questions that got mixed up.** They are separate, and any answer to
one works with any answer to the other:

- **The architecture:** which tree the parser produces, and which trees are
  worked out from which. This is the "source of truth" question. It decides
  what the tools can do and where a grammar change has to be made.
- **The mechanism:** how the parser's code writes a tree down. Either each
  parsing function returns a finished node (today), or it only notes "a
  `match` starts here … and ends here" in a list, and the tree is put
  together afterwards (the "marks" or "events" technique, which the Rust
  library rowan made well known). This is an implementation detail. It
  doesn't decide the architecture: marks can feed one tree or two.

The earlier note's option 3 ("the parser emits marks as a second output")
named an architecture (two trees from one parse) by its mechanism (marks).

**The recommendation.** As the end state: **one lossless tree is the
parser's only output, and the compiler's tree is worked out from it by a
separate, small "lowering" step** (architecture A2 below). The formatter,
the editor and the sweeps read the lossless tree; the compiler reads the
lowered tree, which looks like today's. Get there in two steps: first the
marks beside today's tree (exactly D3559's recommended answer, so the
formatter plan doesn't change), then move the building of the compiler's
tree out of the parser, with the first step's output as the test for the
second.

**What it should do.** One place that knows the grammar, and one that knows
the shorthand (`let (a, b)`, chained comparisons). Tools that ask the tree
for "the arms of this match" instead of scanning lines. Later, an editor
that keeps working inside a half-typed declaration, which today's parser
drops whole. Speed is not at stake: lexing and parsing 1.3 MB of library
source takes about 0.05 s [measured], so the whole repo (6.8 MB) parses in
about a third of a second, and doubling that would not be noticed beside
checking.

## 1. What each reader needs

| Reader | Needs | Must not have |
|---|---|---|
| **Compiler** (`crates/elab`, 87 files use the tree, about 940 places match on an expression's kind [source]) | Meaning only: shorthand already expanded, brackets gone, a position for every error | Comments, commas, spacing; anything that makes those 940 places more complicated |
| **Formatter** (D3558) | Every token and comment, grouped by construct, exactly as written: `let (a, b) = e` as a `let`, three-part tuples as one thing, brackets where the author put them | Any expansion: it can't print `%chain12` or a `match` the author never wrote |
| **Editor** (`crates/lsp`) | Two kinds of thing. *Meaning at a position* (hover, go to definition, rename, inlay hints) comes from the checker's index by position, not from any syntax tree, and stays that way [source: `driver/src/nav.rs`]. *Shape at a position* (the outline, folding, expand selection, "the match under the cursor", where a declaration ends) needs every construct's start and end | To wait: it reparses on each keystroke |
| **Quick fixes and sweeps** | To find a construct, replace or extend it, and get laid-out text back. Today "add missing arms" scans lines for `\| ` at a column (`lsp/src/arms.rs`); the binder sweep walks the tree and the tokens side by side, refuses when a comment is in the way, and lays out "roughly" (`driver/src/binder_sweep.rs`); `doc` reads the tree and the tokens side by side too [source] | Hand-written text scanning per tool |
| **Half-written code** | A tree for the parts that are fine, with a marked gap where the error is, so the rest still gets checked, highlighted and completed | Today: a declaration with a syntax error is left out whole (only its signature is kept if the header parsed); a lexical error empties the file [source: `parse_module_recovering`] |
| **Reparsing while typing** | Not to redo the file. Stitchwort already has this cheaply: a file is cut into declarations at column 0 and each is parsed on its own [source: `split_decls`], and a 150 KB file parses in about 6 ms [estimated from the probe] | A clever incremental tree: not needed at this speed |
| **The Stitchwort formatter** (SW-3145, the formatter written in Stitchwort) | A tree simple enough to define in Stitchwort and to compare with the Rust one node by node: "a kind and a list of children" is one small data type | To port the compiler's tree and its shorthand expansion |
| **Smaller readers** | `doc` (headers as written), the outline and code lenses (which declarations a file has), `search` and `eval` (parse one expression), syntax highlighting (tokens) | |

Goals and types shown in error messages are printed from the checker's own
terms, not from a syntax tree; they are outside this question.

**What today's tree is.** `ast.rs` calls itself "the surface syntax tree, as
written by the user", but it is halfway between written and expanded
[source]. The parser turns `let (a, b) = e` into a `match` (tagged
`MatchKind::Let` so errors can still say "let"), a chain of comparisons into
a hidden `let %chain…`, `.f a` into a lambda over `%section`, `(a, b, c)`
into nested pairs, and text with `${…}` into `++`. The elaborator then
partly undoes two of these: `chain.rs` puts the operand back when the chain
is a proposition, and `patlet.rs` turns the `let`-match into projections.
So neither the formatter nor the compiler gets quite the tree it wants.

## 2. The architectures

Each is an end state. "Lossless tree" means: its leaves are the tokens with
their comments, its nodes are the constructs, and reading it left to right
gives back the file.

**A. One lossless tree is the parser's only output.** Everything else comes
from it. Two variants, differing in what the compiler reads:

- **A1: the compiler reads the lossless tree itself**, through typed
  accessors ("this node is a match; give me its arms"). *Roslyn* (C#) does
  this: the binder walks the syntax tree and produces a separate "bound
  tree"; shorthand is expanded after binding. *Lean 4* too: its `Syntax`
  objects (a kind, children, and the original whitespace on each token) are
  what the elaborator takes in, and macros expand shorthand as
  syntax-to-syntax rewrites that keep the source positions. *TypeScript* is
  a near relation: one tree for the compiler, the editor and the formatter,
  with a node for every bracket; comments are not stored but re-read from
  the text between tokens when wanted. [all from memory]
- **A2: a lowering step turns the lossless tree into a separate compiler's
  tree.** *rust-analyzer*: the parser emits marks, a tree builder makes the
  lossless tree (rowan), typed accessors sit on top, and a lowering step
  makes the tree the type checker uses, keeping a table from each lowered
  node back to its syntax node. *Swift* is moving here: its new parser
  builds only the lossless SwiftSyntax tree, and a step called ASTGen
  builds the compiler's tree from it. [from memory]

**B. Two trees built side by side in one parse.** Each parsing function
builds the compiler's node and also records the lossless structure. Neither
tree comes from the other; they agree because the same code made both.
*Swift's first attempt (libSyntax)* was this, inside the old C++ parser; it
was later removed in favour of A2 [from memory: I recall the cost of
keeping both in every parsing function, and the slowdown, as the reasons].
D3559's recommended answer is this architecture.

**C. One typed tree, made faithful, with comments attached.** Keep a tree
like today's but stop it losing things: nodes for brackets, the shorthand
kept as written, each node knowing its range of tokens; comments either
hung on nodes or kept in a list by position. *Go* (`go/ast` with comment
groups, printed by `go/printer`), *Zig* (nodes index into the token list;
`zig fmt` and the compiler both read it), *Gleam* and *OCaml with
ocamlformat* (the compiler's tree plus comments placed by position).
*rustfmt* is the weak form: rustc's tree, with comments fished out of the
source text between nodes. [from memory] The known trouble is Go's: once a
tool edits the tree, comments placed by position drift to the wrong node; a
whole library (`dst`) exists to work round it. And Go's compiler doesn't
use `go/ast` at all: it has its own parser. [from memory]

**D. Today's tree, plus token-level tools.** What Stitchwort has: the
formatter works on tokens and lines with the parser as referee; each tool
finds its own structure. *clang-format* is the famous case, forced on it by
C++.

**E. Two parsers.** One for the compiler, one for tools. *rustc and
rust-analyzer* (two parsers and two trees for one language, kept in step by
effort), *tree-sitter* grammars in editors, *elm-format*, Go as above.
[from memory] The earlier note already rejected this; so do I. One case of
it is wanted on purpose: the Stitchwort formatter's parser, which is the
point of that project.

### The mechanism, separately

| Mechanism | What it is | Used with |
|---|---|---|
| **Direct construction** | Each parsing function returns the finished node. Stitchwort's parser today: about 180 functions in 5,470 lines, some 90 of which return a node or an error [source: counted outside the tests] | Roslyn (A1, lossless nodes), old Swift (B, both trees), Go and rustc (C), Stitchwort (D) |
| **Marks (events)** | Parsing functions return nothing; they append "start match", "token", "finish" to a list. A separate builder turns the list into a tree, or the list with the tokens *is* the tree | rust-analyzer (A2); D3559's option (B: marks for one tree, direct construction for the other) |
| **How the tree is stored** | Typed (an enum per construct), generic (kind + children), rowan's and Roslyn's two-layer "green/red" trees (built so an edit reuses most of the old tree), or flat arrays over the tokens (Zig) | Any of the above |

What matters about marks for us: they fit Stitchwort's parser well, since it
never moves backwards [source: `pos` is only ever advanced], and a marks
parser recovers from errors easily, because a function that hits an error
records an "error" node and carries on; with direct construction each of
those 90 functions must invent a value to return. Green/red trees and the
rowan library are *not* needed: their purpose is reusing most of a tree
after an edit, and Stitchwort already reparses one declaration at a time,
in milliseconds.

## 3. Pros and cons for Stitchwort, by end state

| | A1: compiler reads the lossless tree | A2: lossless tree, compiler's tree lowered from it | B: two trees from one parse | C: one faithful typed tree | D: today |
|---|---|---|---|---|---|
| **Simplicity** | Fewest trees, but the 940 matching places in the elaborator all work through accessors and skip brackets and commas | Three plain parts, each with one job: parser (grammar only), lowering (shorthand only), elaborator (as now) | Fewest new lines. But every parsing function does two jobs for good, and the compiler's tree stays half-expanded | One tree. But it must serve the formatter (wants everything) and the elaborator (wants little); either the elaborator skips the extras or a second typed tree appears, which is A2 with more types | Simplest parser; the complexity is in the tools (`layout.rs` 1,356 lines, `binder_sweep.rs` over 1,000) |
| **One source of truth** | Yes | Yes: a grammar change is made in the parser; the lowering fails to compile or its test fails until it follows | No: two outputs kept in step by tests (same tokens for certain; same structure only if a test compares them) | Yes | Yes for the compiler; each tool has its own idea of structure |
| **Error positions and messages** | Every construct has an exact range, brackets included | The same: each lowered node carries the identity of the node it came from, so hidden names and expanded shorthand point at what was written | As today (most nodes have spans; applications, operators and pipes work theirs out from their parts) | Good | As today |
| **Editor features** | Best | Best: shape from the lossless tree, meaning from the checker's index, linked by node identity | Good for shape. Linking a checker's complaint to a lossless node is by matching positions | Fair: typed trees are awkward for "walk up from the cursor" | Text scanning |
| **Editing and refactoring tools** | Find the node, replace its text, reformat | Same | Same for reading; fine in practice | Risk of Go's comment drift if tools edit the tree rather than the text | Each tool lays out its own output |
| **Speed and memory** | Parsing is about 25 MB/s today; the whole repo is about 0.3 s [measured]. A lossless tree might double that [estimated]. Negligible | Same, plus a lowering pass, still far under 1% of a check [estimated] | No cost when the marks are off | No cost | No cost |
| **Half-written code** | Natural: error nodes | Natural: error nodes in the lossless tree; lowering turns them into holes the checker already understands (`?`) | Hard: the direct-construction half still gives up at the first error, so the compiler loses the declaration even if the marks describe it | Hard: a typed tree has no place for "three stray tokens" | Declaration dropped |
| **Stitchwort formatter (SW-3145)** | Ports the grammar-only parser; compares trees as text | Same, the easiest port: no compiler's tree, no shorthand | Must port the parser with its compiler half stripped out by hand | Must port the typed tree (about 100 node kinds) | Ports the line-based design, which D3558 retires |
| **Shorthand (`let (a, b)`, chains, `.f` sections, tuples)** | In the elaborator, or as Lean-style rewrites | In lowering, all in one file; the parser records what was written | Stays in the parser's compiler half; the lossless half shows what was written | Must move out of the parser, to the elaborator or a pass | In the parser, partly undone in the elaborator |

Three things the table shows:

1. **Speed doesn't separate the options.** The earlier note's reason for
   option 3, keeping tree building "out of the compiler's normal path", is
   worth a third of a second across the whole repo.
2. **For the formatter alone, A2 and B are equal.** Both give it a lossless
   tree from the one parser. They differ in what the *compiler's* tree is
   built from, in whether half-written code can be handled, and in how many
   jobs each parsing function has.
3. **C is the tempting shortcut and the wrong one here.** The compiler's
   tree would have to stop expanding shorthand and start carrying brackets,
   which pushes formatter concerns into the elaborator's 940 matching
   places.

## 4. Recommendation

**End state: A2.** The parser produces one lossless tree and nothing else.
A lowering step produces the compiler's tree from it. The formatter, the
editor's shape features, the quick fixes, the sweeps, `doc` and the
Stitchwort formatter read the lossless tree. The elaborator reads the
lowered tree and barely changes.

Why A2 and not B, judged as end states (D2303):

1. **One job per part.** Today a parsing function knows the grammar, builds
   compiler nodes and expands shorthand; under B it would also place marks.
   Under A2 it knows the grammar only. Syntax changes are frequent here and
   made by agents, so "one obvious place for each kind of change" is worth
   a lot.
2. **Half-written code.** Only A lets the compiler keep checking a
   declaration with a syntax error in it. B can't, because the compiler's
   half still stops at the first error.
3. **Shorthand gets a home.** The lowered tree can be fully expanded and
   honest about it, instead of halfway; the as-written form is always
   available from the node it came from.
4. **It is where the others ended up.** Swift tried B and moved to A2;
   rust-analyzer, Roslyn, TypeScript and Lean all have a single parse
   output [from memory]. I know of no tool that chose B as its resting
   place.

Why A2 and not A1: the elaborator is 87 files written against a small,
typed, expanded tree, and that is the right tree for it. A1 would make
every one of them aware of brackets and commas for no gain to the user.

**Mechanism:** marks, with a generic tree (kind + children, comments on the
tokens as `lex_with_trivia` gives them now), stored plainly per
declaration. No rowan, no green/red. Typed accessors where they make the
lowering and the formatter's rules readable.

### Staging

Lane hours are [estimated].

| Step | What | Test | Model | Hours |
|---|---|---|---|---|
| 1 | **Marks beside today's tree** (architecture B, as a waypoint). This is stage 1 of the formatter plan, unchanged, with two additions: a kind for every construct including the shorthand as written, and a test that every span in the compiler's tree is the range of some lossless node | Every file reads back from its tree; compiler's tree and hashes unchanged | Opus | 15–25 (already in the formatter plan) |
| 2 | The formatter (stages 2–5 of its plan) and the tools (stage 6) on the lossless tree | As that plan says | as planned | as planned |
| 3 | **Lowering**: write the step from the lossless tree to the compiler's tree. Step 1's parser is the oracle: for every file in the repo, lowering must give exactly the tree the parser builds directly | Trees equal over the repo and the reject examples' error text unchanged | Opus | 25–40 |
| 4 | **Delete the direct construction** from the parser: parsing functions return nothing. Each lowered node carries the node it came from | Hash snapshots unchanged | Opus | 8–12 |
| 5 | **Error nodes**: recovery inside a declaration; lowering turns a gap into a hole. Its own design note first (which errors to recover from; cascades) | New examples under `reject/`; the editor keeps its answers for the rest of a broken declaration | Opus | 15–25 |

Steps 3–5 don't block the formatter and can wait for it to land. Step 3 is
safe in an unusual way: the old and new routes run side by side over the
whole repo until they agree exactly, before anything is deleted.

### What it means for D3559 and the formatter plan

- **D3559's answer doesn't change: the second output (marks).** What
  changes is what it is called and where it leads. It is the first half of
  A2, not a rival to "rewrite the parser". The formatter plan's stages,
  estimates and gates stand.
- Step 1 should be briefed as "the lossless tree", not "extra marks for the
  formatter": every construct gets a kind, including ones the formatter has
  no rule for yet, because the lowering will need them all.
- The formatter's safety check ("same tree before and after") can compare
  lossless trees with the layout taken out, instead of printing the
  compiler's tree as text, which is 85% of `fmt`'s time today (SW-3145's
  finding (the formatter written in Stitchwort)).
- For SW-3145 (the formatter written in Stitchwort): its parser is a port
  of the grammar-only parser, and the two can be compared by printing both
  trees as text, file by file, long before either formatter's output
  matches.

## 5. What I did not check

- How other tools work is from memory throughout, as marked. The Swift
  history (libSyntax removed, ASTGen replacing the old route) is the claim
  the recommendation leans on most; worth a ten-minute check before it is
  quoted elsewhere.
- I searched the parser for places it moves backwards and found none; I did
  not read all 5,470 lines. A function that parses something as an
  expression and then re-reads it as a binder or pattern would need its
  node's kind changed after the fact, which marks allow.
- The "might double parse time" figure is a guess; the "about 25 MB/s
  today" figure is one probe.
- I did not look at how the web playground (`crates/web`, `crates/js`) uses
  the tree beyond noting that it does.

## 6. Questions for Matt

**D3559 (restated): where does the formatter's tree come from?** From the
existing parser, as a lossless tree recorded beside today's compiler tree
(marks). Same answer as before; now understood as step 1 of the end state
below, whichever way D3562 goes. **[rec: yes, the second output]**

**D3562: is the end state "one lossless tree, with the compiler's tree
worked out from it"?** *The problem:* with two trees built side by side,
every grammar change is made twice in one function, shorthand stays half
expanded in the parser, and a declaration with a syntax error can't be
checked at all. *The change:* after the formatter lands, the parser stops
building the compiler's tree; a lowering step builds it from the lossless
tree (steps 3 and 4, 33–52 lane hours [estimated]). *What it should do:*
nothing visible by itself; it makes the parser single-purpose and makes
D3563 possible. The alternative is to stop at step 1 for good. **[rec:
yes]**

**D3563: should the editor keep working inside a declaration with a syntax
error?** *The problem:* while a line is half-typed, the whole declaration
disappears from checking: no errors, hovers or completions for its other
lines, and only the first syntax error in it is shown. *The change:* error
nodes in the lossless tree, turned into holes for the checker (step 5,
15–25 lane hours [estimated], with its own design note). *What it should
do:* the rest of the declaration stays checked while you type. It matters
to a person in the editor much more than to agents, who fix one error and
rerun. **[rec: yes, but last, and only if you feel the lack in VS Code]**

## Findings worth tickets

- `ast.rs`'s header says the tree is "as written by the user"; it holds
  five expansions (`let` patterns, chains, sections, tuples,
  interpolation). The comment could say so.
- `chain.rs` and `patlet.rs` in the elaborator each undo part of an
  expansion the parser made. Under any option, those two could be
  expanded once, in the place that knows whether expansion is wanted.
- The formatter note (and this lane's brief) say the parser has "about 340
  parsing functions": that count includes the roughly 180 test functions
  in the same file. Outside the tests there are 179, of which 141 are
  parser methods. Its stage 1 estimate may be a little high for that
  reason.
- A lexical error anywhere empties the whole module
  (`parse_module_recovering`): one bad character loses every declaration's
  diagnostics. Recovering per declaration there looks cheap, since the
  file is already cut at column 0.
- `doc`, `lens`, `decl_regions` (LSP) and the binder sweep each pair up
  declarations with their tokens in their own way: four users waiting for
  "the declarations of this file, with their tokens" from one function.

## Appendix A: the probe

Eight largest `std/List/*.sw` files concatenated three times (1.33 MB,
23,150 lines), with a declaration that doesn't parse added at the end, so
that `stitchwort fmt --check` lexes (with comments) and parses every
declaration and then refuses the file before any formatting or tree
comparison. Two runs: 0.07 s wall, 0.05 s user each; the same command on a
one-line file: 0.02 s. So about 0.05 s for 1.33 MB, roughly 25 MB/s. Load
average 3.6. Files in
`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3155/`.
