# The parser's end state, now that it has one job

**Status:** design note, 14 November 2026 (SW-3233, for D3579). Paper lane:
nothing is built. One question for Matt ([§9](#9-question-for-matt)).
It follows [syntax-tree-lowering.md](syntax-tree-lowering.md) (SW-3160,
done today: the parser records only marks) and sits beside
[syntax-error-recovery.md](syntax-error-recovery.md) (SW-3161; S0 done, S1
running as SW-1983).

Claims are marked **[source]** (read at `dc26a104f`), **[measured]** (the
main checkout's release binary, built 15:46 today at `f2cb6e48e`; probes in
`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3233/`)
or **[estimated]**.

> **Found on the way, and urgent: `main` checks the wrong statement for a
> common shape** [measured]. `theorem t (a b c q: Prop): a ∧ b ∧ c → q`
> is checked as the statement `a ∧ b ∧ c`: the `→ q` is silently lost. So
> are `↔ q` and `; e` after any chain of three or more `∧`/`∨` operands
> (and after `a ∨ b ∧ c`). `check` accepts
> `theorem bad (a: Prop) (h: a ∧ a ∧ a): a ∧ a ∧ a → False := h`. The
> kernel is not fooled (it proved what it was given), but what was proved
> is not what was written. It came in with lowering L5 this morning; no
> file in the repo has the shape, so no gate saw it. It is a direct product
> of the design question this note is about; [§2](#2-the-bug-and-what-it-shows)
> has the cause and the fix (stage T0, 2–3 h, should not wait).

## In plain words

**The problem.** The parser reads a declaration's tokens and has to say how
they group: these seven tokens are a `match`, these three inside it are an
application. It does not build a tree to say so. Each time it finishes a
construct it writes down a *mark*: a kind and a token range, "tokens 12 to
19 are a `Match`". When the declaration is done, a builder sorts the marks
and nests them into the tree the formatter and the compiler read.

That design was chosen when the marks were a second output beside a parser
that still built the compiler's tree itself. To stay out of that parser's
way, and to keep its stack use small, marking took some shortcuts:

- An operator such as `+` doesn't know where its left operand started. It
  *guesses from the list of marks*: "the last mark that ends here must be
  my operand".
- A few places write marks out of order, or go back and change a mark
  already written.
- The builder tolerates all of that: it sorts whatever it gets, and if two
  marks overlap in a way that can't nest, it quietly drops one and counts
  it. Only a developer tool looks at the count.
- Where the old parser inspected the tree it had built ("is this type an
  equation?"), the new one has no tree, so it builds a small one from its
  marks on the spot, or searches the mark list.

The first three together are today's bug: one function writes the marks of
`a ∧ b ∧ c` innermost last, the `→` after it guesses its operand is
`b ∧ c`, its own mark then overlaps, the builder drops it, and the compiler
never sees the arrow.

**The change.** Keep marks. They suit this parser: a mark carries its own
start, so wrapping an operand already read needs no machinery, and a
construct that fails partway simply never writes one. But make them strict:

1. One way to write a mark: "from the place I remembered, to here, is an
   X". The place is a number the parsing function keeps, not a guess from
   the list. No writing out of order, no going back.
2. The builder checks instead of tolerating: marks arrive in the order
   constructs finish, so one pass nests them, with no sort, and a mark that
   doesn't fit is a compiler error on that declaration, not a silent drop.
3. The parser stops asking its own output questions. Checks about meaning
   move to the lowering, where the tree exists.

**What it should do.** Nothing a user sees, when the parser is right: the
tree is the same tree, byte for byte, for every file in the repo (that is
the test). What changes is what happens when the parser is wrong: today, a
different statement is checked without a word; after, `check` stops with an
internal error at that declaration. For the recovery work, two hazards its
note has to design around go away (an `Error` node mistaken for an operand;
half-open operators to undo). Parsing gets about 2–3 ms faster on std's
69 ms [estimated from a measured 4.1% for the sort]. The deepest nesting
the parser accepts drops by at most 8% (18,264 brackets to about 16,900)
[estimated from measured frame sizes], well above the 12,000 the benchmark
needs.

## 1. What is there now [source]

- **Marks** (`tree.rs:339`): `{ kind, start, end }` in tokens. The parser's
  whole output for a declaration is `DeclMarks` (`tree.rs:347`): the root's
  kind, the marks, and two flags.
- **The builder** (`build_decl`, `tree.rs:704`): drops empty marks, sorts
  by start, then longest first, then latest first (`:713`), nests with a
  stack, skips a mark that covers the whole declaration (the root is passed
  separately), and counts a mark that crosses its parent as *dropped*
  (`:739`).
- **The tree** is flat: nodes in preorder, each with its token range and
  where its subtree ends. Single tokens are leaves with no node. This note
  does not change it.
- **Recording** in the parser, about 160 sites [measured, grep]:

  | Call | Sites | What it does |
  |---|---|---|
  | `node(start, kind)` with `let start = self.mark()` | 99 | "from the token index I kept, to here" |
  | `node_at(span, kind)` (`parser.rs:1032`) | 44 | the same, but the function kept a `Span`, so the token index is found again by binary search (`record_at`, `:1037`) |
  | `open(kind)` … `close()` (`:1075`, `:1089`) | 7 | an operator: the start is read back from the marks (`operand_start`, `:1057`) and parked on a heap stack until the right operand is read |
  | `node_around_operand(kind)` (`:1068`) | 1 | read-back, recorded at once |
  | `operand_start()` used directly | 5 | `sequence`, `iff`, `logic_chain`, `pipe_chain`, `widen_section` |
  | `retag_last` (`:1125`) | 1 | changes the last mark's kind and start (`exists` reuses a lambda's mark) |
  | `widen_section` (`:1137`) | 2 | finds an earlier `Section` mark, empties it (`end = start`, which the builder then filters) and records a wider one |
  | `mark_param` (`:1104`) | — | records unless the last mark already covers the same range |
  | `record_range(start, end, kind)` (`:4163`) | 2 | any range, any order (`mark_logic_chain`, `:4143`) |

- **Reading the marks back for decisions**: `absurd_in` (`:1239`),
  `or_with_absurd` (`:3131`), `rewrite_membership` (`:3596`),
  `callable_paren` (`:4790`), each a scan of the list for marks with given
  ends.
- **Lowering inside the parser**: `lowered()` (`:1168`) copies the marks in
  a token range, builds a one-off `SyntaxFile`, and runs the lowering on
  it, for 22 call sites that want a span "as the compiler's tree has it" or
  a fact about the lowered expression (`is_equation`,
  `declarations.rs:422`; `type_synonym`'s search of an application's spine
  for an annotation, `declarations.rs:462`; `written_start`, `:4222`, which
  decides which line a pipeline's indent is measured from).

## 2. The bug, and what it shows

`logic_chain` (`parser.rs:4120`) reads `a ∧ b ∨ c …` in a loop and then
records all its `Binary` nodes at once (`mark_logic_chain`, `:4143`). For
the last group of operands it records outer before inner, so the last mark
written is the innermost (`b ∧ c`), not the whole chain. Whatever comes
next and takes the chain as its left operand (`→` at `:3705`, `↔` at
`:3773`, `;` at `:3746`) asks `operand_start`, gets `b`, and records a node
from `b` that crosses the chain's own node. The builder drops it. The
lowering's `ResultType` reads "the expression after `:`"
(`lower/access.rs:44`), finds the chain, and never looks at the `→ q` lying
flat beside it.

[measured] with `dev tree` and `check` on one-line files:

| Written | Marks dropped | Goal the checker shows |
|---|---|---|
| `a ∧ b → q` | 0 | `a ∧ b → q` |
| `a ∧ b ∧ c → q` | 1 | `a ∧ b ∧ c` |
| `a ∨ b ∨ c → q` | 1 | `a ∨ b ∨ c` |
| `a ∨ b ∧ c → q` | 1 | `a ∨ b ∧ c` |
| `a ∧ b ∨ c → q` | 0 | `a ∧ b ∨ c → q` |
| `a ∧ b ∧ c ↔ q` | 1 | `a ∧ b ∧ c` |
| `(a ∨ b ∧ c) → q` | 0 | right |
| `(a \|\| b && c; 3)` as a `Nat` | 1 | "expected `Nat`, but this has type `Bool`" |

Four separate safeguards each had to miss for this to reach `check`, and
each is a property of the present design, not of this one function:

1. **The operand's start is a guess that depends on what every other
   function wrote last.** Nothing in `iff` or `expr_inline` is wrong.
2. **Recording is free-form**, so a function can break the "operand is
   marked last" rule without anything noticing: the sort repairs the order
   for the tree, and hides the disorder from the next reader of the list.
3. **A dropped mark is a statistic.** Only `dev tree` exits 1 on it
   (`cli/src/main.rs:161`); the compiler's entry points ignore
   `TreeStats::dropped`.
4. **The lowering doesn't notice unread children.** A slot is found by its
   introducing token (right, for recovery), and nothing checks that what is
   left over is allowed.

The oracle that compared the old route with the new, the span check and
the rolling whole-repo gate all passed, because the repo has no statement
of this shape [measured: 0 marks dropped over 2,620 files]. A test over a
corpus can't stand in for an invariant the code itself keeps.

## 3. The options

**(A) Today:** free-form marks, sorted and nested afterwards.

**(A′) Strict marks (recommended):** marks kept, with three rules.
*Record only at the end:* `node(start, kind)` covers `start..here`; there
is no other way to write one, and no way to change one. *Starts are
values:* a function that may wrap what it reads keeps `let start =
self.mark()`, as 99 sites already do. *The builder checks:* marks arrive in
finishing order (ends never go back; of two with the same end the later
contains the earlier), so one pass with a stack nests them and computes
subtree ends; a mark that breaks the order or crosses another fails the
declaration with `E-INTERNAL`.

**(B) In-order events with `precede`** (rust-analyzer): the parser emits
`Start`, tokens and `Finish` in source order; a construct that turns out to
wrap an earlier one links a new `Start` in front of it (`precede`,
"forward parent"); a `Start` not needed is abandoned and left as a
tombstone. One pass builds the tree, and nesting is right by construction.

**(C) Build the tree directly:** each parsing function returns its node, or
pushes onto a builder with checkpoints (rowan's `start_node_at`).

**(D) Other things looked at:** a parser that never fails (rust-analyzer's
functions return nothing and recover locally); a table of each kind's
allowed children, checked over every tree.

### 3.1 Why not B

B's two mechanisms answer problems marks don't have here.

- *`precede`* exists because a `Start` event has a fixed place in the
  stream. A mark names its own start, so wrapping an operand already read
  is the ordinary case: `node(start, Binary)`. B would add the forward-link
  and the tombstones to get what `node` does today.
- *Single tokens are leaves in this tree* (a name has no node). B can only
  `precede` a finished node, so every operand would need a `Start` up front
  that is abandoned if nothing wraps it, or names would have to become
  nodes (513,279 nodes in the repo would roughly double [estimated]; the
  formatter and lowering read this tree).
- *Errors unwind here.* The parser's functions return `Result` and use `?`
  at several hundred places; recovery catches at a few points
  (`recover_to`). A mark design needs nothing undone when a function fails:
  it never wrote its mark. In B, every `Start` since the snapshot that has
  no `Finish` must be found and abandoned. That is the `open` stack again,
  for every construct instead of seven operators.

What B gives that A lacks, nesting that can't be wrong, A′ gets from the
checking builder: not by construction, but at the first parse that breaks
it, in any build.

### 3.2 Why not C

With a flat preorder tree, "build directly" has no good direct form: a
parent isn't known when its first child is finished (`a` in `a + b`), so
either nodes are inserted in front of already-written ones (a shift per
wrap: quadratic on a long `a + b + c + …`), or nodes are written as they
finish and reordered once at the end. The second *is* A′: a strict list of
marks is the tree in finishing order, children before parents. So C is
either A′ under another name, or a pointer tree with an allocation per node
(slower [estimated 5–10% of parsing], and a second tree type for the
formatter and lowering to convert from). In Stitchwort itself, where
functions return values freely and there is no stack to protect, C is the
natural shape (self-hosted-fmt.md §3.2 stands). In Rust it isn't.

### 3.3 Why not leave A

[§2](#2-the-bug-and-what-it-shows). And recovery makes each weak point
worse: see [§5](#5-recovery).

### 3.4 D

- **A parser that never fails** would be a rewrite of every error path for
  no gain: layout already gives recovery its resume points
  (syntax-error-recovery.md §2.4).
- **A table of allowed children per kind** is worth having, later (stage
  T4): it turns "tokens lying flat where a node should be" into an error
  wherever it happens, which the span check only does where a compiler span
  happens to point. It is also the written grammar of the tree that the
  self-hosted formatter's twin (SW-3228) and the recovery work ("which
  children may be absent") both need.

## 4. The comparison

| | A today | A′ strict marks | B events | C direct |
|---|---|---|---|---|
| **A wrong start for an operand** | possible from any function's recording order; silent | not possible: the start is a local of the function that records | not possible | not possible |
| **Crossing or misordered nodes** | dropped, counted in a dev tool | internal error on that declaration, in every build | can't be expressed | can't be expressed |
| **Ways to record** | 9 (table in §1) | 1 | 4 (start, finish, precede, abandon) | 1–3 |
| **A construct whose kind is known late** | `retag_last`, `widen_section` edit earlier marks | the kind is passed in, or the mark is written by the caller that knows | `precede`, or change kind at finish | return value |
| **A failed construct** | leaves nothing, except operators left on `open` | leaves nothing | leaves open `Start`s to abandon | leaves builder state to unwind |
| **Parser lines for marking** [estimated] | — | about 120 fewer (`open`/`close`, read-back, relabelling, `record_at`, `mark_logic_chain`), about 25 `let start` added | about 160 sites rewritten | all 5,300 lines of parser touched |
| **Tree build** | sort + nest: 8.4% of parse-and-lower, the sort 4.1% [measured] | one pass, no sort: about 4–5% [estimated] | one pass: about the same [estimated] | none separate; per-node allocation |
| **Stack per nesting level** | 1,377 bytes per bracket [measured] | at most +112 bytes [estimated] | the same as A′, or more (a marker per frame) | more: nodes held across calls |
| **What lowering and the formatter see** | the tree; `signature_kept`; a `dropped` count | the same tree; neither extra | the same tree | a different type, or the same after conversion |

### 4.1 Parse time [measured]

`dev tree --time` on std (98 files, 2.1 MB, 169,503 nodes), best of 7,
machine load 8–15: parse and lower 78.9 ms, lossless tree alone 51.4 ms
(L6 measured 69.0 and 46.4 ms on a quieter machine). A 12-second sample of
250 rounds of parse-and-lower (`sample`, 7,656 samples in the parse):

| Part | Share |
|---|---|
| Lexing, with comments | 19.4% |
| The parser | 40.3% (of which writing marks about 2%, bracket matching and the declaration split 4.4%) |
| The tree builder | 8.4% (the sort 4.1%; copying and nesting the rest) |
| The lowering | 26.9% |
| Other | 5% |

So the sort costs about 3 ms of std's parse and 9 ms of the whole repo's
235 ms. Speed is not a reason to choose between these designs. The sort
goes in A′ because a builder that sorts can't tell disorder from order,
and disorder is what [§2](#2-the-bug-and-what-it-shows) was.

### 4.2 Stack [measured, then estimated]

The parser gets half the stack (`parser_limit`, `parser.rs:281`): 24 MiB
of `dev tree`'s and `check`'s 48. Deepest nesting accepted, by binary
search: `(((…)))`, `f (f (…))` and `(1 + (1 + …))` 18,264 levels, so 1,377
bytes a level; lists 15,518 (1,621 bytes); lambdas 15,701; `if` 14,542.

Frame sizes from the release binary's function prologues: `atom` 400
bytes, `expr_inline` 304, `range_expr` 288, `app` 192, `cmp_expr` 96 or
more, `unary` 80, and `expr`, `add_expr`, `mul_expr`, `append_expr` 32
each. A `u32` kept across a call needs at most one more saved register
pair, 16 bytes, in the functions that don't have a spare one. Seven
functions on the path would wrap an operand: at most 112 bytes on 1,377,
8%, so about 16,900 levels [estimated]; the benchmark needs 12,000 and
October's parser managed 12,740. The 44 `node_at` sites keep a 12-byte
`Span` today only to avoid keeping a 4-byte token index, and would get
smaller.

Reading the operand's start back from the marks was a sound trade when the
parser's frames also held the trees it was building and the limit was
tight. It now buys at most 8% of depth, and four functions that have
nothing to do with it hold 1,184 of the 1,377 bytes
([Findings](#findings-worth-tickets)).

## 5. Recovery

What S2–S5 need, against each design:

- **`Error` and `Gap` nodes over skipped tokens.** In A and A′ a recovery
  point writes `node(from, Error)`. Constructs that finished inside the
  skipped range are already in the list and nest inside it. Same in both.
- **Absent children** (R1: nothing after `:=`). No node, in any design.
  In A, an absent operand is a trap: `operand_start` answers "the token
  before", which belongs to something else. The recovery note avoids it by
  rule (R1 only where nothing follows). In A′ there is no such question.
- **The operand hazard** (syntax-error-recovery.md §3.2): an `Error` mark
  ending just before an operator would be taken for its operand, so R2b
  may only skip where an operand starts, and S3 carries a test for it. In
  A′ the hazard doesn't exist and the rule is only a choice.
- **`snapshot` / `recover_to`** (`parser.rs:868`, `:1744`, `:1759`):
  restores the modes and truncates `open`. In A′ `open` is gone, so a
  snapshot is the modes.
- **Marks that must not survive a recovery.** S1's `recovering_body`
  (SW-1983, uncommitted, read today) already filters the list after a
  failure: marks starting at the body's first token "would cross" the
  `Error` node, "so they go". That is the builder's tolerance being
  programmed around by hand. With a checking builder the rule has to be
  stated once: a recovery point's `Error` node starts where the failed
  construct started, so what finished inside nests in it. S2–S3 add five
  more recovery points; each would otherwise repeat the filtering.
- **Checks on meaning that are still parser errors** stop the parse where
  recovery then skips text. "A block must end with an expression, not
  `let`" (`parser.rs:2666`) is the state of every block while its last
  line is being typed. In the lowering it is a missing result with the
  whole block still in the tree; in the parser it is an error for R3 or R6
  to skip around [source; how S2 will treat it I didn't check].

## 6. Leftovers from the two-route period [source]

Found by reading `parser.rs` (to line 5,326, where its tests start),
`parser/declarations.rs`, `tree.rs`, `lower.rs` and the mark readers'
call sites. Not a full census of every error site: T2 should sweep.

**Read-back and free-form recording** (go in T1):

| What | Where |
|---|---|
| `operand_start` | `parser.rs:1057`; used at `:1081`, `:1069`, `:1138`, `:3746`, `:3773`, `:4122`, `:4189` |
| `open` stack, `open`/`close`, `node_around_operand` | `:900`, `:1075–1098`, `:1068`; sites `:3275`, `:3705`, `:4486`, `:4527`, `:4538`, `:4550`, `:4592`, `:4612` |
| `Snapshot::open` | `:868–871`, `:1747`, `:1761`, test `:5362` |
| `node_at` / `record_at` (binary search for a token index the caller could have kept) | `:1032–1040`, 44 sites |
| `retag_last` | `:1125`, used `:3808` |
| `widen_section`, and the empty mark it leaves | `:1137–1158`, used `:3712`, `:4209`; the filter `tree.rs:709` |
| `mark_param`'s test of the last mark | `:1104–1117` |
| `record_range`, `mark_logic_chain` (the bug) | `:4163`, `:4143–4160` |
| The sort, the dropped count | `tree.rs:713`, `:739`, `:398`, `:433` |
| The root passed twice: as `decl()`'s return value and as a mark the builder skips | `declarations.rs:124`, `parser.rs:2243`, `:2749`; `tree.rs:728` |

**The parser asking its marks what it parsed** (T2):

| What | Where | End state |
|---|---|---|
| `absurd_in`, `absurd_since` | `parser.rs:1231–1260` | the pattern functions return whether they read `()` (it decides whether `=>` is required: the parser's business) |
| `or_with_absurd` | `:3131` | a check on meaning: the lowering |
| `rewrite_membership` | `:3596` | the lowering (the body's node is a `Membership`) |
| `callable_paren` | `:4790` | `atom` knows what it just read; returns it |
| `lowered`, `lowered_span`, `lowered_pattern_span`, `enum Lowered` | `:1168`, `:1206`, `:1216`, `:680` | deleted with their callers' moves |
| …for a message's span | `declarations.rs:373`, `:393`, `:696`; `parser.rs:2330`, `:2345`, `:2519`, `:2761`, `:3201`, `:3304`, `:3850`, `:4346–4403`, `:4958` | the check moves to the lowering, which has the span |
| …for a decision | `is_equation` `declarations.rs:422`; `type_synonym` `declarations.rs:462`; `written_start` `parser.rs:4222`; `operand_text` `:4432` | lowering, except `written_start`, which is layout and should read tokens |
| `use crate::ast::{Expr, Pattern, BinOp, …}` and `crate::lower::…` in the parser | `parser.rs:23`, `:26`; `declarations.rs:11` | the parser imports neither |

**Values returned only to feed checks on what was grouped** (T2; each check
is the lowering's by `parser.rs:6–8`'s own rule):

| What | Where | Feeds |
|---|---|---|
| `BinderRead` (6 fields) | `parser.rs:705`; built `:2557`, `:3941`, `:3967` | misplaced attributes (`:2254`, `:2262`, `:2310`, `:2474`, `:3641`), "must be `auto`" (`:2265`), "needs a name" (`:2276`), "an interface can't have indices" (`:2330`), defaults (`:2517`), "can't be `auto`" (`:2406`) |
| `ParamRead` | `declarations.rs:47` | a lambda's or quantifier's default (`parser.rs:3303`, `:3848`) |
| `DefinitionRead` (`unfolding`, `body`, `result`) | `declarations.rs:38` | a local definition's `unfolding` and missing body (`parser.rs:2750–2764`); `kind` stays |
| `Line` | `parser.rs:687` | "a block must end with an expression" (`:2664–2673`) |
| `braced_fields` → count | `:2437` | "declares no fields in its braces" (`:2383`) |
| `list_expr` → the first spread | `:4910` | "a list of facts can't have a `..`" (`:4955`) |
| `FirstAttribute` | `:697` | the messages above; half of its uses are grouping (attributes with nothing after them, `:347`) and stay |
| Checks in `definition` that read nothing but kinds | `declarations.rs:286`, `:307`, `:391–398` | "an instance can't have `decreasing`" / `unfolding`, "an instance needs a body" |

**The kept signature** (goes with S1's R6, or in T3 if S1 leaves any):
`keep_header`, `header_kept` (`parser.rs:886–894`, `:420`, `:430`;
`declarations.rs:250`, `:339`); `signature_kept` (`tree.rs:355–359`,
`:381`, `:757`, `:793–799`; set `parser.rs:441`, and `false` at seven other
constructions of `DeclMarks`); the lowering's reading of it
(`lower.rs:230`). S1's working tree still passes a `kept` flag [source,
SW-1983's uncommitted diff].

**Things in `parser.rs` that aren't parsing** (T3):

- Module assembly and the rule for which error wins: `lowered_module`,
  `unlowered_error` (`:196–252`). The lowering's
  (`lower.rs:41–51` documents the rule; the code is here).
- The entry points, each building a `SyntaxFile` and lowering it:
  `:63–189`, `namespace_line` `:546–585`, `parse_expression_tree`
  `:596–652`. A front module (`parse.rs`): lex, parse, build, lower.
- Names of a declaration that failed, read off its tokens:
  `failed_names_in` (`:143`, which re-lexes a copy of the text padded with
  as many spaces as the declaration's offset, to keep positions),
  `declared_names_of` (`:465`), `failed_names_of` (`:530`); the lowering
  calls back into them (`lower/decls.rs:95–110`). Their own small module.
- The tests: `parser.rs:5,328–9,196`, 156 tests with 444 uses of the
  compiler's tree's constructors and none of the lossless tree
  [measured, grep]. They test the parser and the lowering together through
  the old route's signature. No unit test pins the parser's own output,
  which is one more reason [§2](#2-the-bug-and-what-it-shows) got through.
  Grammar tests should compare tree dumps; the rest belong with `lower/`.

**Comments that describe the old route or a stage** (T3):

| Where | Says |
|---|---|
| `tree.rs:68–72` | marks "could be relabelled from a saved list length the same way": an option nobody took |
| `tree.rs:72–73` | "nothing has to be undone" after a failed parse: untrue once S1's `recovering_body` filters marks |
| `tree.rs:75–87` | the read-back, as the design |
| `tree.rs:89` | "for now" an `Error` root (S1 changes it) |
| `parser.rs:9–10`, `:1160–1166` | lowering "on the spot" |
| `parser.rs:40–46` | the `Result` box, explained by `Result<Expr>` frames; no function returns an `Expr` now (the box is still right: an unboxed `Result<()>` would be 112 bytes) |
| `parser.rs:1050–1056`, `:1072–1074` | read-back as the reason for small frames |
| `parser.rs:1087` | an error "drops the declaration's marks": it doesn't, they stay under the `Error` root |
| `parser.rs:902`, `:1742`, `:1757`, `:1767`, `:5394` | "stage S0", "come in stage S1" (S1 removes them) |
| `parser.rs:2138`, `:2769`, `:3740`, `:3767`, `:3792`, `:3828`, `:4560`, `:4821` | what a construct lowers to (`Iff p q`, `%section.name`, `Bool.not`): the lowering's doc |
| `lower.rs:9`, `:28`; `tree/spans.rs:5` | "(step 4)", "the ones the parser used to give", "step 3" |
| `lower/coverage.rs:3–5` | the oracle's history: commit-message material |
| `lower/exprs.rs:847`, `lower/binding.rs:643`, `lower/matching.rs:241` | tests named by lane ("lane L1", "L3", "L4") |

## 7. Recommendation

**A′: keep marks, make them strict**, and finish moving meaning out of the
parser. In one sentence for the module doc: *the parser's output is the
tree's nodes in the order they finish; each is written once, by the
function that read it, from a start that function kept; the builder only
reorders, and refuses what doesn't nest.*

The gate for every stage is the one SW-3228 named for the twin: `dev tree
--print` is identical before and after for every file in the repo
(513,279 nodes in 27,588 declarations [measured]), reject examples
included, and the hash snapshots don't move. A lane runs it on the one
namespace it is working in; the whole-repo comparison is the verifier's or
Overmind's.

## 8. Stages

Lane hours [estimated]. The parser is core language work, so Opus (D2506).

| Stage | What | When | Model | Hours |
|---|---|---|---|---|
| **T0** | The fix. `logic_chain` records its nodes outermost last (or with `open`/`close`, like the other operators). A dropped mark fails its declaration with `E-INTERNAL` at every entry point, and is a debug assertion. Tree-dump unit tests for each loose operator (`→`, `↔`, `;`, a section's widening) after each chain shape in [§2](#2-the-bug-and-what-it-shows)'s table; one reject-free example file with them. `task fuzz:syntax` asserts no dropped marks | **Now.** It doesn't wait for S1: a few lines in one function and one in `SyntaxFile::build`; small conflict risk with SW-1983, which hasn't touched `logic_chain` | Opus | 2–3 |
| **T1** | Strict marks: starts as values; `open`, `close`, `operand_start`, `node_around_operand`, `node_at`, `record_at`, `record_range`, `retag_last`, `widen_section` and `mark_param`'s read-back gone; the builder takes finishing order, one pass, no sort, and checks; the root is the outermost mark; `Snapshot` loses `open`; S1's mark filtering restated as "the `Error` node starts where the failed construct did". Nesting re-measured and recorded (performance log) | **After S1 merges, before S2 starts** | Opus | 6–9 |
| **T2** | The parser stops reading its output: the checks in [§6](#6-leftovers-from-the-two-route-period-source)'s second and third tables move to the lowering with their messages; `lowered()` and the `…Read` structs go; the parser no longer imports `ast` or `lower`. Which of two errors in one declaration is shown may change (D3574's rule) | After S3 | Opus | 6–8 |
| **T3** | Housekeeping: entry points and module assembly out of `parser.rs`; failed-name scanning in its own module; grammar tests rewritten as tree dumps, the rest moved to `lower/`; the comments in [§6](#6-leftovers-from-the-two-route-period-source); `signature_kept` and its flags if S1 left them | Any time after T1; beside S4 (the editor, which isn't in the parser) | Sonnet, reviewed by the orchestrator | 3–4 |
| **T4** | The table of allowed children per kind, checked in debug builds, `dev tree` and the fuzzers; the lowering refuses a child it didn't read | After S3, when "which children may be absent" is settled | Opus | 4–6 |

Total 21–30 lane hours.

**T1 goes before S2–S3**, at the cost of S2 starting one lane later
(6–9 h):

- S2 and S3 add five recovery points (R3, R5, R4, R2, R2b) in the same
  functions T1 rewrites (blocks, arms, brackets, operators). Done in the
  other order, each point is written against `open` and the read-back,
  with the §3.2 hazard's rule and its own mark filtering, and then
  rewritten.
- The checking builder is a test S2–S3 get for free: a recovery point that
  writes a node which doesn't nest fails in its own lane's tests, not in a
  corpus run later.
- They can't run side by side: both lanes would rewrite the same few
  hundred lines.

**T2 goes after S3**: S2–S3 settle which errors a recovered declaration
reports (one a line, the first), and the moved checks have to follow that
rule, not anticipate it. T2's cost of waiting is small: S2–S3 may call
`lowered_span` at a few new sites.

## 9. Question for Matt

**D3582: the parser keeps marks, made strict; it does not move to
rust-analyzer's events or to building the tree directly.**
*The problem:* marks were added as a second output beside the old parser,
with shortcuts (operands found by reading the mark list back, marks
written out of order or changed afterwards, a builder that sorts and
quietly drops what doesn't fit). Today those shortcuts made `check` accept
`a ∧ b ∧ c → q` as the statement `a ∧ b ∧ c`.
*The change:* keep marks, because they fit a parser whose functions fail
by returning early, and because a mark names its own start. Remove the
shortcuts: one way to write a mark, from a start the function kept; a
builder that checks order and nesting in one pass and makes a misfit a
compiler error; meaning checks out of the parser. Stages T0–T4, 21–30 lane
hours, T1 between recovery's S1 and S2.
*What it should do:* the same tree for every file (the gate). A parser
mistake of today's kind becomes an internal error at that declaration
instead of a different theorem. Recovery's S2–S3 lose two hazards. About
2–3 ms off std's 69 ms parse [estimated]; nesting depth down by at most 8%
[estimated].
*The alternative:* rust-analyzer's events get correct nesting by
construction, at the price of about 160 rewritten sites, tombstones for
every unwrapped operand, and undoing open events at each recovery point.
**[rec: yes, strict marks]**

**Decided here as the orchestrator's kind of call** (say if you disagree):
T0 is a bug fix and starts at once. A dropped mark is an internal error in
`check`, not a count. T1 goes between S1 and S2. The sort goes because it
hides disorder, not for its 4%.

## Findings worth tickets

- **`a ∧ b ∧ c → q` is checked as `a ∧ b ∧ c`** ([§2](#2-the-bug-and-what-it-shows)),
  since L5 (`ee2664063`, 11:54 today). Stage T0. Until it lands, any
  theorem checked today whose statement has `→`, `↔` or `;` after three or
  more `∧`/`∨` operands was checked against the shorter statement; the
  repo has none [measured].
- **A dropped mark should fail `check`**, and `SyntaxFile::build` should
  assert none in debug builds, so every existing test and fuzz run looks
  for one. Part of T0.
- **The lowering ignores children it didn't read** (`ResultType` took the
  first expression after `:` and left `→ q`). A per-kind "nothing left
  over" check, or T4's table.
- **No test pins the parser's own output.** `parser.rs`'s 156 tests go
  through the lowering. A grid of tree-dump tests (each operator after
  each operand shape) is cheap and would have caught this. Part of T0,
  then T3.
- **`range_expr` (288 bytes), `expr_inline` (304), `atom` (400) and `app`
  (192) hold 1,184 of the 1,377 bytes a nesting level costs** [measured,
  prologues]. `range_expr` is on every expression's path for a rare
  construct; moving its body out of line, as `logic_chain` is, would buy
  more depth than the read-back ever saved [estimated: 15–20%]. Depth, not
  speed, so not covered by D3465's pause; still low priority.
- **`failed_names_in` (`parser.rs:156`) allocates a copy of the text
  padded with one space per byte of offset** to lex a failed declaration
  in place: for a lexical error near the end of a 100 KB file, 100 KB per
  attempt, twice. A lexer entry point that takes a starting offset would
  do.
- **"A block must end with an expression, not `let`" is a parse error**
  (`parser.rs:2666`), so under recovery the commonest half-typed block is
  one R3 or R6 skips text for. Worth a look by the S2 lane before T2
  moves it.
- **`a ∧ b ∨ c ↔ False` prints its goal as `a ∧ b ∨ c ↔ False = True`**
  [measured], and `a ↔ False` as `a ↔ False = True`: it reads as
  `(a ↔ False) = True`. Presumably the `Bool` `False` made a proposition;
  I didn't check. Either the printer needs brackets there or the statement
  isn't the one meant.
- `docs/proposals/README.md` lists syntax-error-recovery.md with "D3581
  open"; it is decided. `syntax-tree-architecture.md` and
  `syntax-tree-lowering.md` aren't listed.
