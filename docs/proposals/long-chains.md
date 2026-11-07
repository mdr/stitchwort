# Long chains: list literals, operator chains and blocks without recursion

**Status:** draft, 7 November 2026 (SW-1993). Waiting for Matt's decisions
D2840 to D2844. Answers D2751 of [deep-input.md](deep-input.md), which set
the policy ("length never costs stack") but left the elaborator and kernel
for this note. Read-only lane: nothing here was measured, and every number
for the playground is an estimate, labelled as one.

## Summary

**The main finding: long list literals already work in the playground.**
D2751 assumed that "a list literal of a few hundred elements is too long" in
the playground. That was true on 15 October and stopped being true on
22 October, when SW-62 cut long literals into short chains joined by a
balanced tree of `append`s (`crates/elab/src/check.rs:4596-4672`). A browser
test checks and runs a 20,000-element literal in the playground build
(`web/tests/browser.mjs:1321-1340`), and SW-62's commit reports 100,000. The
note in `crates/web/build.rs:16-18`, the two `resource` expectations in
`web/stress.html:142-143`, and deep-input.md §3A and D2751 all date from
before it. Text literals are compact terms (`Term::Chars`), so they have no
limit either (`nesting.rs:217-229`: four million characters check).

So the gain D2751 hoped for is mostly there already. What is left:

1. **List literals: right length, wrong shape.** Whether a literal is
   chunked depends on the stack of the thread checking it
   (`check.rs:4606`: `count <= limits.stack / LITERAL_BYTES`). The same
   1,000-element literal is one `Cons` chain on the command line (64 MiB
   thread, chunked above about 20,000), and chunks joined by `append` in a
   test (2 MiB, above about 650) and in the playground (above about 110). So
   its term, and its content hash, depend on where it was checked, and the
   chunked form costs about 200 evaluation steps an element (SW-332). The fix
   is small and needs no kernel change: split long literals with `let`s at a
   fixed size, as Lean does.
2. **Blocks are the real remaining limit.** Every line of a block nests the
   rest of the block inside it, in the syntax tree, in the elaborator's
   recursion and in the term, so every pass recurses once per line. In the
   playground I estimate a block of about 90 `let` lines, or fewer inside
   other code, runs out. A long `main` is the most likely thing a user writes
   that hits a length limit today. Fixing it means a loop down the *last
   child* in the elaborator's block code and in every pass over terms: about
   eight lanes, two of them in the kernel. I recommend measuring first and
   deciding on the number.
3. **Operator chains** (`a + b + …`, `xs ++ ys ++ …`, `|>`, `&&`) are limited
   at an estimated 60 to 90 terms in the playground and about 10,000 on the
   command line. Right-nested ones come for free with the block work.
   Left-nested ones (`+`, `-`, `*`) nest in a function's *first* argument;
   I recommend keeping them guarded, with an error that suggests
   `[…].sum`.

## 1. What a user hits today

Plain version first. A playground user who writes

```
def main () : {IO} () :=
  IO.print "line 1"
  IO.print "line 2"
  …                      -- a hundred lines like this
```

gets "ran out of resources: the program is nested too deeply for the type
checker", although nothing in it is nested: it's just long. The same goes
for a `def` with a hundred `let` lines, or a sum of a hundred numbers. A list
of a hundred thousand numbers, by contrast, checks and runs.

**Estimated limits.** The measurements are from stack-safe-evaluation.md,
step 4 (15 October, a native release build on a 2 MiB thread, whose limit is
1.5 MiB, `budget.rs:104-112`). I scale them two ways. On the command line
(48 MiB limit) I multiply by 32. In the playground (a 256 KiB guard,
`web/build.rs:23`, applied in `web/src/lib.rs:40-46`) I multiply by
256/1536 × 1.5, where the 1.5 is build.rs's "the same bytes natively are
less depth" (`web/build.rs:20-22`). The scaling reproduces the 15 October
playground figures at 128 KiB (about 220 list elements against the measured
200; nesting about 30 against 25), so I'd trust it to within a factor of 2.
The elaborator's frames have grown since then, so the true numbers are
probably lower. **Confidence: low to medium.**

| Chain | Native, 2 MiB (measured) | CLI, 64 MiB (est.) | Playground (est.) |
|---|---|---|---|
| list literal | any length (chunked) | any length | any length; 20,000 tested |
| text literal | any length (compact) | any length | any length |
| `let` lines in a block | 354 | ~11,000 | ~90 |
| effectful lines (`IO.print …`) | not measured | not measured | probably below the `let` figure (more frames per line, §2.4) |
| `+` chain | 297 | ~9,500 | ~75 |
| `++` chain | 345 | ~11,000 | ~85 |
| application arguments `f a b c …` | 260 nested; a long flat spine not measured | — | ~65 nested |

These are budgets for the whole declaration: a block inside a function
inside a `match` has less.

## 2. The map: every walk a long chain goes through

For each walk: does its depth grow with the chain's length, what stops it
today, and how it could loop. "Guarded" means it calls `budget.nesting`, or
`budget.step`, which also checks the stack (`budget.rs:614`), and fails with
`E-RESOURCE`.

### 2.1 A list literal `[1, 2, …, n]`

| Walk | Where | Depth grows with n? | Today | To make it loop |
|---|---|---|---|---|
| Parse | `parser.rs:4573` | no: a loop into `Expr::List(Vec<Expr>)` | fine | done |
| Syntax drop, span | `ast.rs:498`, `:457` | no: flat `Vec` | fine | done |
| Elaborate items | `check.rs:4570-4594` | no: one `check` per item, in a loop | fine | done |
| Postponed number literals (K4) | `numbers.rs:355` `queue_number` | no: one queued problem per item, resumed from a queue | fine | done |
| `may_perform` over items | `effects.rs:2249-2276` | no: a loop over items | fine | done |
| Build the term | `check.rs:4596-4672` | **chain depth min(n, stack/2400)**, then 64 + log₂(n/64) | chunked when long | see §3 |
| Kernel `check` | `core/check.rs:459` → `check_ctor_fields` (`:556`) | yes, once per `Cons` in a chain | guarded (`:424`) | last-child loop (§3.D) |
| Zonk, fold back, shift | `unify.rs:2850`, `:2549`; `term.rs:548` | yes, per `Cons` | guarded | last-child loop |
| Evaluate | machine, `Fields` frames on the heap | no | fine | done |
| `append` at check time | the prelude's `append`, run by the machine | frames grow with the left half | frame limit 2,000,000 | gone with §3.B |
| Conversion, quotation, unification's comparison | work lists (stack-safe step 3) | no | fine | done |
| Printing | `pretty.rs:780`: a loop down a `Cons` chain | no | fine | done |
| Hash | `hash.rs` work list | no | fine | done |
| Check cache write, read | `cache/codec.rs:272` (work list into a node table), `:591` (by node number) | no | fine | done |
| Term and value drop | `term.rs:235`, `value.rs:428` | no | fine | done |
| Lowering, runtime compile | `rt/src/lower.rs` (guarded); `code.rs` (unguarded, SW-1895) | per `Cons` in a chain | guarded, except SW-1895 | last-child loop |
| JavaScript | `js/src/lib.rs` `expr`, `tree` (guarded) | per `Cons` in a chain | guarded | last-child loop |

With chunking, every "yes" above is bounded by 64 plus a logarithm once a
literal is long, so none of them limits length. They limit the *unchunked*
chains, which is why the threshold must be below what the smallest stack can
take, and why it is computed from the stack.

### 2.2 A left-nested chain: `1 + 1 + … + 1`

The parser's `add_expr` and `mul_expr` loop (`parser.rs:4151-4181`), but
build `Binary(Add, Binary(Add, …), 1)`, as deep as the chain is long.

| Walk | Where | Depth grows? | Today |
|---|---|---|---|
| Syntax span | `ast.rs:404-432`: a loop down each side | no, but O(n) per call | fine |
| Syntax drop | `ast.rs:498` loop | no | fine |
| Group the chain | `numbers.rs:709` `Group::tree`, `:813` `map_leaves` | yes | guarded |
| Check the leaves | `numbers.rs` `group_with`, a loop over `leaves` | no | fine |
| Build the term | `numbers.rs:1774` `build` | yes | guarded |
| The term | `Loc(App(App(add, ‹rest›), 1))`: nests in the first explicit argument | — | — |
| Kernel `infer` on `App` | `core/check.rs:318`: infers the head, then checks the argument | yes, through the argument of the inner `App` | guarded |
| Every later term pass | as in 2.1 | yes | guarded |

`Group::tree`, `map_leaves` and `build` are simple tree walks and would be
easy to loop. But that alone gains nothing: the kernel, then lowering, then
the JavaScript generator would each stop at about the same length. The nesting
is in a non-last argument, so the last-child loop of §3.D doesn't reach it.
Changing the term's *shape* (re-associating the chain) is out: `(a + b) + c`
and `a + (b + c)` aren't convertible when `a` is stuck, so `rfl` and goals
would change. A `let`-split (§3.B) keeps the meaning but puts `let`s into
propositions, which users see in statements and goals (§3.B, against). So I
recommend leaving these guarded (D2844).

### 2.3 Right-nested chains: `++`, `|>`, `&&`, tuples

- `++`: the parser recurses, guarded (`parser.rs:4139-4148`, `deeper()`).
  The elaborator's `append` infers the left side and checks the right side
  (`check.rs:4811`), recursing down the right. The term is
  `append a (append b …)`: it nests in the **last** argument.
- `|>`: the parser loops (`parser.rs:3840`) into a left-nested
  `Pipe(Pipe(x, f), g)`, and `infer_pipe` (`pipe.rs:44`) recurses into the
  value. The term `g (f x)` nests in the last argument.
- `&&` and `||`: the parser loops (`parser.rs:3785`) and builds a right-nested
  tree; the term `And a (And b …)` nests in the last argument (inferred from
  the shape; I didn't trace the logic elaborator).
- Tuples `(a, b, c, …)`: right-nested `Tuple` (`ast.rs:129`), terms nest in
  the last field.

All of them nest in the last child of the term, so a last-child loop in the
term passes covers them. In the elaborator, `++` and `|>` each need their own
loop (two small functions); `&&` and tuples go through the generic
`check`/`infer`.

### 2.4 Blocks

A block is parsed in a loop (`parser.rs:2162-2183`), then folded from the
right into `Let { value, body }`, `Seq(line, rest)` or `LocalDefs { body }`,
each line holding the rest of the block. Then:

- **Pure lines**: `check` on `Let` elaborates the value, binds the name,
  checks the body, then builds `Term::Let`. That's one guarded recursion per
  line.
- **Effectful lines** (`IO.print …` in `main`): `comp_check_in` on `Seq`
  (`effects.rs:2713-2748`) elaborates the line, then calls `sequence`
  (`effects.rs:3148`) with a closure that elaborates the rest. So each line
  costs several Rust frames: `comp_check_in`, `sequence` and the closure. The
  term is the line's computation bound to a continuation `λ_. rest`, which
  nests in a lambda in the last argument.
- **Kernel**: `Term::Let` checks the value, then the body, then rebuilds
  (`core/check.rs:351-358`, `:530-537`). The continuation is a `Lam` in the
  last argument of an `App` (`:318`).
- **Every later pass** (zonk, `map_vars_with`, termination, lowering, the
  runtime's passes, JavaScript) recurses once per line.
- **Quadratic work per line**, which a loop wouldn't remove by itself. The
  kernel calls `body.mentions(0)` at every `Let` (`core/check.rs:356`,
  `:535`). That is a work-list walk of the whole rest of the block
  (`term.rs:705`), so a block of n lines costs about n²/2 node visits.
  Computing a `Seq`'s span walks down the chain (`ast.rs:404-432`), and the
  elaborator does it at each level. At 10,000 lines this is about 50 million
  steps, which is tolerable; at 100,000 it isn't. A loop that removes the
  stack limit must also compute these once per block, bottom-up.

## 3. The designs

### A. Keep what there is: chunk by the stack, guard the rest

- **For:** list and text literals have no length limit; nothing to do.
- **Against:** a literal's term and hash depend on the thread. A def with a
  1,000-element literal hashes differently in `stitchwort check` and in
  `cargo test`, and differently again in the playground, which matters for
  the check cache, the hash snapshots and the bound-prelude pins if such a
  literal is ever in std or the examples. (I didn't search the `.sw` files
  for one; the stage below checks.) It meets D2543 in letter, since the
  meaning is the same, but a content hash is an output too. The chunked form
  costs about 200 steps an element each time it is evaluated (SW-332:
  `rfl` on 20,000 elements went from 720,069 to 4,856,399 steps), and the
  playground pays that above about 110 elements. Blocks stay at about 90
  lines in the playground.

### B. Shallow terms by construction: split long literals with `let`

**What it is:** the elaborator never builds a chain deeper than a fixed
size. A literal longer than 64 elements is built as Lean 4 builds its list
literals. As I recall Lean's `%[a, b, …|tail]` helper, it splits the elements
in half, binds the second half, `let rest := %[second half|tail]`, and builds
the first half onto `rest`, recursively. So the term is at most 64 deep plus
twice the logarithm, and has no function calls. (I checked Lean's `Prelude`
for the exact threshold and didn't find the macro there; medium confidence on
the details, high on the idea.)

- **For:**
  - The term is the same on every thread and build, so the hash is too.
  - Evaluating it costs a step per `let` (n/64 of them), not 200 per element.
  - No kernel change: `Term::Let` already exists and is checked and evaluated
    everywhere, so it adds nothing to the trusted base.
  - It's one function in `check.rs`, replacing the `append` tree. Spreads
    (`[..xs, y]`) still need `append`, as now.
  - It works for every right-nested *data* literal built the same way
    (`NonEmptyList`, through `non_empty_literal`, `check.rs:4086-4140`).
- **Against:**
  - The items in the first half sit under the new binders, so each is
    shifted, once, by its total depth.
  - Where a definition's body term is printed as written (hover on a local
    definition's value, goal-as-written), a split literal would show its
    `let`s. That's the same as today's `append`s. The printer can recognise
    the shape and print one literal (an implementation detail for the
    stage).
  - It doesn't help blocks or left-nested arithmetic. For arithmetic it would
    put `let`s inside propositions. `theorem : 1 + … + 1 = 100` would have
    `let`s in its stored statement, which `rewrite` and the printer see. Not
    worth it for sums.

### C. A compact kernel term for list literals (`Term::List`)

**What it is:** `Term::Chars` generalised. A literal is one node holding its
element terms, `Term::List(elem_ty, Rc<[Term]>)`, with a value
`Value::List(Rc<[Value]>, start)`. Its meaning is its expansion into `Cons`,
and every operation commutes with that, as for text (`core/src/chars.rs:1-27`).
Quotation could even turn a long `Cons` value back into one node, so goals
and results showing long lists would stay shallow.

- **For:** depth 1 for every pass, whatever the length. Less memory: one
  slice instead of n cons cells. Quick hashing and caching.
- **Against:** a trusted-base change much bigger than `Chars`. `Chars` is
  closed (characters, no variables), so shifting, substitution, `mentions`,
  zonking and the termination checker never look inside it. A list literal's
  elements are open terms, so every binder-aware walk (about fifteen of them,
  §3.D) gets a new case, and so do kernel checking, conversion against an
  expanded list, unification, the pattern compiler's matching (`step`), the
  equation compiler's "smaller argument" rule
  (`a_compact_list_is_never_a_smaller_argument`), lowering, JavaScript and
  the cache's codec. B gets the same depth for long literals with none of
  that. The memory and speed gains matter only for very large literals, and
  large data comes from `include` or text, which is compact already.
- **Rules out nothing:** B's terms can be read as compact later, if ever
  wanted.

### D. Loops along the last child, in every pass

**What it is:** each recursive pass handles its *last* child in a loop
instead of a call, keeping a small stack of "what to do after" frames on the
heap. Recursion stays, under the guard, for the other children. Kernel
`check` on `Let x v body` checks `v`, pushes a frame (`x`, the type, `v`,
unbind afterwards), and continues the loop with `body`. When the loop
reaches a leaf, it pops the frames and rebuilds the terms inside-out. The same
goes for `Loc`, `Ann`, a `Lam` body, the last argument of an `App`, and the
last field of a `Ctor`. The printer already does this for `Cons` chains
(`pretty.rs:780`) and for application spines (`:1886`, `:1920`).

- **For:** it covers every right-nested chain at once: blocks, effectful
  blocks (the continuation is a `Lam` in the last argument), `Cons` chains of
  any length (no chunking at all), `++`, `|>`, `&&`, tuples. Depth then grows
  only with *real* nesting, which is what rule 2 of deep-input.md wants.
- **Against:** many passes. In the term passes: kernel `infer`, `check` and
  `check_ctor_fields`; `Term::map_vars_with` (shift and instantiate,
  `term.rs:548`); `fold_back`, `zonk_changed`; the termination checker;
  `erase`; lowering, `opt`, `trmc`, `specialise`, the runtime's `compile`
  and `validate` (`rt/src/`); the JavaScript generator. In the elaborator:
  `check` on `Let` and `LocalDefs`, `comp_check_in` and `sequence` for
  effectful blocks, `append`, `infer_pipe`. The elaborator's part is the
  hard one. `sequence` takes the rest of the block as a closure and builds
  the bind *after* it returns, and error handling wraps the rest
  (`effects.rs:2740-2747`: an error on the next line is reinterpreted when
  the line was missing an argument). Both have to become frames. The order
  in which unknowns are created and solved must not change
  (stack-safe-evaluation.md §1), which a frame-for-frame translation keeps,
  but the reviewer must check it. It also needs the quadratic work of §2.4
  removed.
- **Not reached:** left-nested chains (first-argument nesting) and long flat
  application spines through the head. Those are rare (D2844).

### E. Smaller frames (headroom)

Shrinking the elaborator's frames (`#[inline(never)]` on cold paths, boxing
large locals) raises every guarded limit by the same factor. It's cheap and
sometimes worth doing anyway, but like a bigger thread it moves the limit
rather than removing it (deep-input rule 5). It's not a design for length.

### Comparison

| | Lists | Blocks | `++`, `\|>`, `&&` | `+`, `*` | Kernel change | Size |
|---|---|---|---|---|---|---|
| A. As now | any length; thread-dependent term | ~90 (pg) | ~85 (pg) | ~75 (pg) | none | none |
| B. `let`-split | any length; one term | unchanged | unchanged | unchanged | none | 1 lane |
| C. `Term::List` | any length, depth 1 | unchanged | unchanged | unchanged | large, trusted | 4-5 lanes |
| D. Last-child loops | any length, no splitting needed | memory | memory | unchanged | yes (`check`, `infer`) | ~8 lanes |
| E. Smaller frames | — | ×1.5–2? | ×1.5–2? | ×1.5–2? | none | 1-2 lanes |

(pg: playground, estimated.)

## 4. Recommendation

**B now, D for blocks if the measured limit is too low, neither C nor
re-associating arithmetic.**

- **B**, because it turns the remaining list-literal problem (a term and hash
  that depend on the thread, and 200 steps an element) into a fixed shape at
  almost no cost, without touching the kernel. It replaces SW-62's and
  SW-332's `append` tree and its stack-dependent threshold, and gives the
  same term on every target.
- **D**, but only after a measurement. Blocks are the length limit a user is
  likely to meet, but I can't measure it in this lane, and the work is about
  eight lanes, two of them in the kernel and one hard one in the elaborator.
  Stage 1 measures it in the playground, for `let` blocks, effectful blocks
  and right-nested chains. If a block of 300 lines in the playground runs out
  (my estimate says about 90), D is worth it; if it doesn't, E's headroom
  may be enough. Once started, D's end state is "length costs no stack for
  right-nested chains in any pass", and the order matters: the elaborator
  first (it's where the guard fires first), then the kernel, then the term
  utilities and backends. Otherwise the limit only moves.
- **Not C**, because B gets the same depth for long literals without adding a
  trusted representation whose elements are open terms. Revisit only if
  someone needs literals in the millions in memory.
- **Left-nested arithmetic stays guarded**, with a better error: when the
  expression that ran out is a long chain of one operator, add a note such as
  "this sum has 5,000 terms; write long sums as a list, `[…].sum`". That's
  rule 2 of deep-input.md with a useful hint. Re-associating would change
  meaning, and splitting would put `let`s in statements.

**What it costs:** B is about an hour. D is about 8 to 10 hours of lanes,
plus review of the kernel part on Opus. Stage 1 is under an hour.

**What it rules out:** a stack-dependent elaborated term (no more
`limits.stack` in the elaborator's output); `Term::List` for now;
re-associating operator chains.

**How we'd know:**
- After B: a 1,000-element literal hashes the same on a 2 MiB and a 64 MiB
  thread (a new test that checks the same file on both); `rfl` on SW-332's
  20,000-element literal takes no more steps than the single-chain version
  did (720,069, give or take the `let`s); `long_list_literals` and its
  small-guard twin still pass at 100,000.
- After D: a block of 100,000 `let` lines, and one of 100,000 `IO.print`
  lines, check on a 2 MiB thread and in the playground (the deep-input
  corpus's block rows move from "E-RESOURCE" to "succeeds"), in time roughly
  linear in the length (10,000 and 100,000 lines checked, within about 15× of
  each other).

## 5. The longest list the playground handles

- **Today:** no stack limit. 20,000 elements are tested
  (`browser.mjs:1326`); SW-62 reported that 100,000 check and run, and that
  the page then spends "most of a minute colouring and indexing the text".
  So the practical limit is the editor's speed, around 100,000 elements, not
  the checker. Above about 110 elements the playground's term is the chunked
  form, at about 200 extra steps an element each time it is evaluated.
- **After B:** the same length, at a step per 64 elements instead of 200 an
  element. The editor's colouring and indexing stays the limit. That's
  outside this note; file it if Matt wants million-element literals.
- **Blocks, today:** about 90 `let` lines (estimate). **After D:** memory and
  time, so tens of thousands at least, once the quadratic `mentions` and span
  work is gone.

## 6. Decisions for Matt

- **D2840:** Answer D2751 like this: list and text literals are done (SW-62
  and compact text); right-nested chains and blocks get loops along the last
  child in every pass *if* stage 1's measurement shows a playground block
  limit under 300 lines; left-nested operator chains stay guarded? **[rec:
  yes, because lists, the case D2751 named, are already solved, and blocks
  are the real remaining limit but cost about eight lanes, so a measurement
  should decide]**
- **D2841:** Replace the stack-dependent chunking with a fixed-size `let`
  split, so a literal's term and hash are the same on every thread and
  build? **[rec: yes, because a content hash shouldn't depend on the stack,
  and it also removes SW-332's 200 steps an element]**
- **D2842:** What length should the playground guarantee for a block, the
  target D is built to? **[rec: no fixed number beyond "limited by memory"
  as the end state, with 100,000 lines in the corpus as the test, because
  any stack-based number would differ by engine]**
- **D2843:** A compact `Term::List` in the kernel? **[rec: not now, because
  `let`-splitting gives the same depth with no change to the trusted base;
  revisit for literals in the millions]**
- **D2844:** Keep left-nested chains (`+`, `-`, `*`) guarded, with an error
  note pointing at `[…].sum`, rather than looping or re-associating them?
  **[rec: yes, because re-associating changes what `rfl` proves, a loop
  would need first-argument frames in every pass, and long sums are rare in
  real code]**

Decided here as implementation details: the split size of 64, the same as
`LITERAL_CHUNK`; shifting each item once by its total depth; the printer
showing a split literal as one literal; in D, the elaborator before the
kernel before the backends; removing the quadratic `mentions` and span work
as part of D, not separately.

## 7. Tickets to file

In order. Stage 1 can start at once; stage 2 after D2841; stages 4 to 8 only
after D2840 and stage 1's numbers.

1. **Measure long chains in the playground, and fix the stale notes**
   (Sonnet, 45 min). Add `web/stress.html` cases, each found by bisection as
   in `nesting.rs:58` at the 256 KiB guard: `let` blocks, effectful blocks,
   `+`, `++`, `|>`, `&&`, tuples. Change lines 142-143 to expect
   `checks: true` (a 20,000-element literal, and 20,000 characters), and
   update the comment in `crates/web/build.rs:16-18` and deep-input.md §3A.
   Report the numbers on the ticket for D2840. Tests: the stress page in
   headless Chrome (only these cases), and `task test:one --
   long_list_literals`. *Asks Matt first if the wasm build plus a browser
   run is over the lane budget.*
2. **`let`-split list literals at a fixed size** (Sonnet, 60 min; Opus
   reviews, since it generates kernel terms, D2364). Replace the `append`
   tree and the `limits.stack / LITERAL_BYTES` threshold in
   `check.rs:4596-4672`; spreads keep `append`; remove `LITERAL_BYTES`.
   New test: one literal of 1,000 elements hashes the same under 2 MiB and
   64 MiB limits. Tests: `task test:one -- long_list_literals`,
   the spread tests (I found no file named for them; search for `[x, ..xs]`), `task snap:hashes`
   and the `hash_stability` test (hashes of examples with literals over 64
   elements change), SW-332's `rfl` step count by hand. Absorbs nothing filed.
3. **A hint for long operator chains** (DeepSeek, 30 min). When an
   elaborator `E-RESOURCE` is raised inside a `numbers::Group` with more than
   1,000 leaves of one operator, add the note suggesting `[…].sum` (or
   `.product`). Tests: a new test in `nesting.rs`'s `long_sums`, and `task
   test:one -- long_sums`.
4. **Elaborator: blocks in a loop** (Opus, 90 min). `check` on `Let` and
   `LocalDefs`, and `comp_check_in`/`sequence` on `Let` and `Seq`, as a
   loop with heap frames; the `missing`-argument error rewrite becomes frame
   data; the order of unknowns unchanged. `append` and `infer_pipe` the same.
   Tests: `task test:one -- long_blocks`, `long_pattern_blocks`,
   `postponement`, and the elaboration tests of effectful blocks it touches.
5. **Kernel: last-child loop in `infer`, `check` and `check_ctor_fields`**
   (Opus, 90 min). `Loc`, `Ann`, `Let` body, `Lam` body, the last `App`
   argument, the last `Ctor` field. The `skip` flag of `Term::Let` computed
   bottom-up once, not by `mentions` at each level. After 4 (otherwise the
   elaborator's guard still fires first). Tests: `task test:lane AREA=core`
   if it fits two minutes, otherwise the kernel tests and
   `deep_terms_in_later_passes`.
6. **Term utilities: last-child loops** (Sonnet, 60 min): `map_vars_with`,
   `fold_back`, `zonk_changed`, the termination checker, `erase`. Tests:
   `task test:one -- nesting`, the unify and termination unit tests.
7. **Backends: last-child loops** (Sonnet, 2 × 60 min): runtime lowering,
   `opt`, `trmc`, `specialise`, `compile`/`validate` (after SW-1895, which
   makes them fallible and guarded), and the JavaScript generator. Tests:
   `task test:lane AREA=rt`, the JS generator's tests,
   `deep_terms_in_later_passes`.
8. **Spans once per block** (Sonnet, 30 min): stop computing a `Seq`/chain
   span at every level in the elaborator (§2.4). Can go with 4. Tests: a
   10,000-line block checks in time within 15× of a 1,000-line one.

The deep-input corpus (deep-input.md stage 1) gives stages 4 to 8 their
rows: each removes "E-RESOURCE" expectations for the block and right-chain
shapes. SW-1874 (`chain`'s `go`, list patterns) and SW-1895 stay as filed;
stage 7 builds on SW-1895.

## What I didn't cover

- No measurements: every playground and 64 MiB number is scaled from the
  15 October native figures (§1), and the scaling factor is from one
  build.rs comment. Stage 1 replaces them.
- I didn't trace the elaboration of `&&`/`||` chains or tuples, or check
  that their terms nest in the last child (inferred from the syntax's shape).
- I didn't search std, the examples and AoC for literals between 64 and
  20,000 elements, whose hashes stage 2 changes. Stage 2's `snap:hashes`
  run will show them.
- List *patterns* (`| [a0, …, a9999] =>`) are SW-1874's, and their
  compilation cost (cubic in depth, stack-safe-evaluation.md) is work, not
  stack. I left them out.
- The editor's colouring and indexing time for very long lines and literals
  (SW-62's "most of a minute" at 100,000) is outside this note.
