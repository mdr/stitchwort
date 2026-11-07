# Syntax identity that doesn't come from the allocator (SW-1801)

**Status:** design note, 7 November 2026, Opus. Nothing implemented. The
decisions are D2575–D2578 (§7). Follows SW-1797 and SW-1800
(`docs/reviews/SW-1800-dot-failed-cache.md`).

## 1. In short

- **The problem.** Two elaborator caches, the dot-call tables `dot_heads`
  and `dot_failed`, remember results by *where a piece of syntax sits in
  memory*. When the elaborator copies some syntax, elaborates the copy and
  frees it, the next copy can land at the same address and find the first
  one's results. Whether it does depends on the heap, so step counts vary
  from run to run (`reads-weaken-over-map-implicits`: 67,836,957 to
  67,837,612 steps over 42 loads).
- **The change.** Give the dot-call syntax a small id of its own, a
  number from one global counter. A copy gets a new number, just as it
  gets a new address today; only reuse goes away. Key the two tables by
  that number instead of the address.
- **What it should do.** The same run gives the same step counts every
  time, and nothing else changes: every lucky hit becomes the miss it was
  on the other runs, and SW-1800 showed that a miss is always right. The
  syntax tree stays the same size (88 bytes a node), and the key shrinks
  from 40 bytes to 8.

The other address-keyed tables don't need this (§2): each one only
compares against syntax that is borrowed while the key exists, so its
address can't be reused while it matters.

## 2. Every table keyed by an address [checked]

Found by grepping `crates/` for `ptr::from_ref`, `as *const`,
`Rc::as_ptr`, `ptr::eq` and `as usize` on syntax.

### Syntax addresses in the elaborator

| Where | What it remembers | How long the key lives | Can a reused address give a wrong answer? |
|---|---|---|---|
| `dot.rs` `call_key` → `Caches::dot_heads` | the head a receiver's dot call resolves to (`T`, `T.f`) | until the next declaration | **Yes, proven.** A hit skips inferring the receiver. Varies the step count today. A wrong one could pick another function. |
| `dot.rs` `call_key` → `Caches::dot_failed` | that a call's prefix form failed, in one metavariable state | until the next declaration | **Yes, proven.** A hit skips `prefix_form` (20 steps in `postponed-lambda-second-error`). A wrong one changes which reading of the call is used, so which term, or which error. |
| `logic.rs:246` `decl.condition` | which expression `logic::condition` is reading as a condition | set before `check(cond)`, put back after | No. `cond` is borrowed the whole time. |
| `logic.rs:201`/`408` `decl.conjunction` | the left side of `a && b`, so its proof can be found on the way | the same | No, for the same reason. |
| `check.rs:5456`/`2803` `decl.app_expected` | which application's last argument should wait for the expected type | set around `infer(expr)`, put back after | No. `expr` is borrowed the whole time. |
| `check.rs:5546` | compares with `decl.condition` | — | No (above). |
| `named.rs:908` `filled_by` | which of the given arguments filled each parameter | one call; both sides are in `args` | No. Both are live in the same slice. |
| `check.rs:546`, `lib.rs:3545`, `effects.rs:4244`, `search.rs:1532`, `module.rs:1307`/`2925` | `ptr::eq` between two live references, or against a static marker | the comparison | No. |
| `cache/codec.rs` `ids`, `seen` | the encoder's numbering of shared `Term`s | one encoding; the terms are borrowed | No. |

So the dot-call tables are the only hazard, and both are proven ones
(SW-1797, SW-1800). The scoped ones are safe by a rule: *a key is set only
while the syntax it names is borrowed*. A live allocation can't share its
address with another, so a match means the same node. What they can do
is miss when the elaborator compares against a *copy*, and that miss is the
same on every run.

### Kernel and evaluator addresses (not syntax)

`core/src/value.rs` keys `CallMemo` and `ShapeCache` by `Rc` addresses, and
`core/src/check.rs` `Unchanged::seen` by slice addresses. Each keeps what
it keys alive (`CallMemo` holds the values, `ShapeCache` its `owners`,
`Unchanged` borrows them), or lasts one traversal. That's the discipline
SW-1800 added to the dot tables, kept already. Nothing to do here.

### Why the dot tables in particular

Their entries outlive the syntax they were made for. Since SW-1800 the
tables are emptied before each declaration, and the queue's resumed checks
are kept alive until then (`Caches::keep_dot_owner`), which closes the two
cases SW-1800 found. A third remains: syntax that the elaborator builds,
elaborates and drops *within* a declaration. For example:

- `pipe::as_call` clones the head and every argument of `x |> f a b`;
- `records::brace_arguments` rebuilds an application around a record
  argument;
- `effects::run_first` and its neighbours (`effects.rs:4293`) rebuild
  calls;
- `check.rs:6521` builds a `Field` chain from a dotted name each time it's
  elaborated;
- `membership.rs:177`, `update_lemmas.rs:227` and the `derive_*` modules
  build syntax too.

There are about 230 places in `elab` that construct an `Expr`, and about
300 clones of syntax. The key already includes the receiver's and the
field's spans, so a reused address hits only for *a copy of the same
source text* (or generated syntax sharing its spans). That's why the
hits in `reads-weaken` are all on one `read.all` in
`std/Parse/Reads.sw`: successive copies of the same lambda. Whether such a
hit is ever *wrong* is unknown. SW-1800's structural-key experiment
suggests it can be, since same text and spans weren't enough for the
derived `ext` lemmas. It is certainly nondeterministic.

## 3. Measurements [measured]

Measured this morning on `lane/SW-1801` (= `main` at 3194220bc), release
build, with temporary instrumentation, since removed.

**Node sizes** (`size_of`): `Expr` 88 bytes, `Name` 40, `Span` 12,
`Pattern` 96, `Decl` 328. `Expr::Field(Box<Expr>, Name)` uses 48 of the
88, so an 8-byte id fits in it with no growth.

**How much syntax.** Parsing all of std (96 files, 1.95 MB of source)
makes 259,441 allocations of 88 bytes, most of them `Box<Expr>`.
Parsing AoC (620 files, 2.9 MB) makes 316,685.

**How full the dot tables get.** From a whole uncached AoC check
(`check --no-cache`, 287 namespaces, 69 s), counted each time the tables
are emptied:

| | total | most in one declaration |
|---|---|---|
| declarations | 11,490 | — |
| declarations with any entry | 5,551 | — |
| `dot_heads` entries | 24,386 | 98 |
| `dot_heads` hits | 8,064 | — |
| `dot_failed` entries | 213 | 6 |
| checks kept alive (`dot_owners`) | 1,551 | 30 |

So the tables are small. Neither the key's size nor its hash matters for
speed: it's at most a hundred entries, about 0.7 hits per declaration.
What matters is only whether a hit is right. The cost of `dot_heads`
missing is real, though: without `dot_failed`, `long_dot_chains_are_cheap`
goes from 5 s to more than 180 s (SW-1800). The fix must keep every hit
on the *same* syntax.

## 4. The options

The requirement, from SW-1800: a cached result stands for one piece of
syntax in one attempt. So the key needs **identity**, not structure. Today
the address is that identity, but only while the syntax is allocated.

### (a) Node ids from the parser, fresh ids for synthesised syntax

Every node (or every node that can be a key) carries a `NodeId`. The
parser assigns them; syntax the elaborator builds gets fresh ones.

- **Where the counter lives.** One process-wide `AtomicU64` in the syntax
  crate, behind `NodeId::fresh()`. Not a counter per parse: ids would then
  be per file, needing `(FileId, n)`, and `SourceMap::truncate` reuses
  `FileId`s after a rewind. That's the same hazard as the address, which is
  why `call_key` carries a source epoch today. Not thread-local either:
  syntax parsed on one thread can be elaborated on another (the test
  harness, the language server). A `u64` never wraps, and a relaxed
  `fetch_add` costs nothing next to building a node.
- **Copies.** This is the real choice (D2575):
  - *A copy keeps its id* (derived `Clone`). Then the pipe's copies of
    `read.all` all share the source's id and hit each other's entries on
    every run. That's deterministic, but more hits than any run has today.
    Whether those hits are right is exactly what SW-1800 couldn't
    establish, and it would move step counts and maybe hashes.
  - *A copy gets a fresh id* (a hand-written `Clone` for `NodeId`). This is
    the address's own rule, minus reuse: a copy is a new allocation, so a
    new identity. Every run then behaves like today's runs where the copy
    missed. A move keeps the id, as it keeps the receiver's box address
    today.
  - **Recommended: a fresh id on every copy.** It changes nothing but the
    luck.
- **Rewrites.** Every construction site writes `NodeId::fresh()`. There's
  no `Default`, so the compiler finds every site; there are about ten that
  build a `Field`.
- **Which nodes.** The full version puts the id on every `Expr`:
  - `Expr` becomes `struct Expr { id, kind }`, or the id goes in every
    variant;
  - 88 bytes become 96, about 2 MB more while std's syntax is held;
  - each of the roughly 1,600 uses of `Expr::` in `syntax`, `elab` and
    `driver` changes.

  Only `Field` needs it now. Every dot call's receiver comes out of an
  `Expr::Field(recv, field)` (`check.rs:2134`, `2185`, `5907`,
  `effects.rs:3509`), and the queue's copy, `DotCall`, would carry its own
  id. So the minimal version is `Field(Box<Expr>, Name, NodeId)`, with no
  growth (§3).
- **Cost.** Small. Parsing or copying a `Field` does one atomic add. The
  key goes from `(usize, Span, Span, usize)`, 40 bytes, to one `u64`,
  because the spans and the epoch only guarded against reuse. The parser's
  tests barely notice: none print a `Field` with `Debug`. The `equivalence`
  shapes print `Debug` with spans hidden, so `NodeId`'s `Debug` prints `_`,
  always, and shapes of separate parses still compare equal.
- **What it guarantees.** Two keys are equal only when they come from the
  same node, or a moved one, never a copy. It holds whatever the allocator
  does, and for syntax built anywhere, because building syntax needs an id
  and the only way to get one is `fresh()`.

### (b) An id per syntax allocation (`Rc` with an id field)

Syntax isn't `Rc`'d; it's `Box`ed and cloned. Moving it to `Rc<Expr>`
with an id would be a large refactor of the whole tree for what (a), with a
fresh id on every copy, already gives: one identity per allocation that
outlives the allocation. The one thing `Rc` adds is cheap sharing instead
of copying. That's a separate performance question, not this one.

### (c) Keep syntax alive per declaration, extended to the synthesised sites

SW-1800's approach, applied to every site that builds syntax and
elaborates it: move the built `Expr` into a per-declaration arena before
elaborating, so it isn't freed until the tables are emptied.

- **Cost:** a change at each of the ~230 construction sites that might
  reach a dot call, plus lifetime plumbing (an arena that hands out
  references while `cx` is borrowed mutably). The memory is small (30
  kept checks at most in one declaration today, §3).
- **What it guarantees:** only what the audit found. A site that's
  missed fails silently, as a lucky hit on some runs, and new sites keep
  appearing (each sugar adds one). It leaves the 40-byte key, the epoch
  and `dot_owners` in place. Not recommended.

### (d) A debug-build check that cached addresses belong to live syntax

Rust can't ask whether an address is live. The practical form stores a
fingerprint of the receiver with each entry (its `Debug` text, say) and
asserts on a hit that the receiver still matches.

That can't find the remaining case. The reused hits are copies of the
*same* source text with the same spans (§2), so the fingerprint matches.
The check would pass exactly where the problem is. It would catch
different syntax at a reused address, which the spans in the key already
rule out except for generated syntax that shares spans. Not recommended,
even as a step towards (c).

### (e) Tables scoped to one outermost dot call

Keep entries only while the outermost `infer_call` runs, as the
`logic.rs` keys do, so the syntax is borrowed throughout. It fails
because syntax is copied and freed *inside* that extent: a pipe or record
rewrite inside a chain's argument. It would also lose the hits across a
postponed call's resume. Not recommended.

### Comparison

| | Change size | Guarantee | Memory | Behaviour change |
|---|---|---|---|---|
| (a) id on `Field`, fresh on copy | ~10 construction sites, `DotCall`, `call_key`; removes `dot_owners` and the epoch | holds whatever the allocator does | none | lucky hits become misses |
| (a) id on every `Expr` | ~1,600 uses of `Expr::` | the same, for every node | +8 B a node | the same |
| (b) `Rc` + id | larger than (a) on every node | the same | varies | the same |
| (c) keep alive | ~230 sites to audit | only where the audit reached | small | the same |
| (d) detector | small | none for the case that remains | none | none |
| (e) scoped tables | small | doesn't hold | none | loses resume hits |

## 5. Interactions [checked]

- **Check cache and replay.** Syntax is never encoded: `cache/codec.rs`,
  `dump.rs` and `rows.rs` store kernel terms and rows, and none of them
  mention `ast`. Ids are not serialised and need not be. A replay doesn't
  elaborate, so it never meets the tables.
- **The language server's rewind (SW-1798).** `Caches::rewind` already
  empties the dot tables. With ids that's for memory only: syntax
  re-parsed after a rewind gets new ids, so old entries can't be hit.
  `source_epoch` exists only to keep addresses from colliding across
  generated source, so it leaves the key.
- **The formatter.** It works on its own tree (`crates/fmt` doesn't use
  `Expr`), so it is unaffected. Its tests that compare `parse_shape`s keep
  working because `NodeId` prints as `_`.
- **Content hashes.** They are hashes of kernel `Term`s (core), and terms
  never contain syntax, so an id can't reach one. Two guards make that
  hold for the future:
  - `NodeId` has `Eq` and `Hash` for the tables, but no way to read its
    number and no serde;
  - its `Debug` is `_`, so even a hash of a `Debug` dump of syntax can't
    see it.

  `hash_stability` stays the test for this.
- **Threads.** The global counter gives unique ids across threads. Ids
  differ from run to run, but nothing orders by them: the tables are only
  looked up, never iterated.

## 6. How other compilers do it [from memory; not re-checked today]

- **rustc.** The AST has `NodeId`s (a `u32` newtype). The parser leaves
  them as `DUMMY_NODE_ID`, and the resolver assigns real ones during macro
  expansion (`next_node_id`), so expanded and desugared nodes get fresh
  ones. Lowering to HIR maps them to `HirId` = (owner item, local index),
  so ids are stable per item for incremental compilation, and side tables
  (`TypeckResults`) are keyed by the local index. Nothing is keyed by
  address. Stitchwort doesn't need per-item stability, since ids never
  persist, so a global counter is enough.
- **Lean 4.** `Syntax` has no ids. Positions live in `SourceInfo`
  (original or synthetic), and the info trees the server queries are
  found by source range. Postponed elaboration is identified by the
  metavariable it will solve (`SyntheticMVarDecl`, keyed by `MVarId` from a
  name generator), not by the syntax. Lean's pointer-keyed caches
  (`PtrSet`, the `instantiateMVars` caches, via `ptrAddrUnsafe`) hold
  the objects they key, the discipline core already follows here.
- **GHC.** No node ids either: locations (`SrcSpan`) on `Located` nodes,
  and `Unique`s for names from a supply. Typechecking work that is put off
  lives in mutable evidence variables, again identified by a fresh unique,
  not by the syntax.

The common thread: identity for postponed or cached work comes from a
fresh-number supply, never from the allocator, and never from the text
alone.

## 7. Recommendation and plan

**Recommendation: (a), minimal.** Add a `NodeId` to `Expr::Field` and to
the queue's `DotCall`, from a global counter, with a fresh id on every
copy, and key `dot_heads` and `dot_failed` by it. Leave the scoped tables
as they are, with a comment stating their rule.

### Stage 1: the dot tables (expected about 90 min, Opus: syntax and caches)

1. `crates/syntax`: a `NodeId` (`fresh()`, a `Clone` that gives a fresh
   id, `Debug` printing `_`, `Eq` + `Hash`, no `Default`, no accessor).
   Add it to `Expr::Field`, and update the parser's and elaborator's
   construction sites, which the compiler lists.
2. `dot.rs`: `call_key` takes the `Field`'s id; `DotCall` stores the id
   it was made with, fresh at `queue_call` because the receiver there is
   a copy. `CallKey` becomes a `NodeId`. The spans and `source_epoch` leave
   the key.
3. `state/caches.rs`: remove `dot_owners` and `keep_dot_owner`; keep the
   per-declaration emptying, now only to bound memory. Update the module
   comment.
4. Comments at `logic.rs:246` and `check.rs:5456` stating the rule that
   keeps them safe (the keyed syntax is borrowed while the key is set).

**Done when:**

- `reads-weaken-over-map-implicits` takes the same steps on every load. Add
  an ignored test beside SW-1800's in
  `crates/driver/tests/elaboration/dot_prefix.rs`,
  `reads_weaken_takes_the_same_steps_every_time`, over
  `same_steps_every_time`.
- `postponed-lambda-second-error` still does
  (`a_postponed_dot_call_takes_the_same_steps_every_time`).
- `pure-fold-in-parse-function`, the third example in SW-1797 that SW-1800
  never reached, gets the same test. If it still varies, the cause is
  elsewhere, and that's a new ticket.
- No hash moves: `hash_stability::{prelude, examples, projects,
  a_namespace_checked_alone_has_the_same_hashes}`.
- `long_dot_chains_are_cheap` stays at about 5 s.
- `call_key_differs_across_generated_source` (`dot.rs` tests) is
  rewritten as "a copy's key differs; the same node's doesn't".
- `size_of::<Expr>() == 88`, asserted in a syntax-crate test.
- The syntax crate's tests and `crates/fmt` `api` (the shape tests) pass.
- Step-count snapshots (`task snap:examples`) may move, all upward to what
  the unlucky runs already took; the lane says which moved.

**What to measure:** each example's spread before and after (loads that
differed / loads), and the AoC uncached check time (69 s today), which
should not move.

### Stage 2, only if wanted: ids on every node

Only if another cache comes to need identity on arbitrary expressions (the
scoped `logic.rs`/`check.rs` keys would then move to ids for uniformity).
Not planned.

### Decisions for Matt

- **D2575:** Should a copy of syntax get a *new* identity (as today's
  addresses do), rather than keep its source's? It's the choice that
  changes nothing but the luck; keeping ids would add hits that SW-1800
  couldn't show are right. [rec: yes, new identity]
- **D2576:** Put the id only on dot-call syntax (`Expr::Field` and the
  queue's `DotCall`) for now, not on every node? Zero memory cost, about
  ten sites against about 1,600. [rec: yes]
- **D2577:** In the same stage, drop what only guarded against reuse:
  `dot_owners`/`keep_dot_owner`, and the spans and source epoch in the
  key? [rec: yes]
- **D2578:** Start stage 1 as a lane on Opus (the syntax crate and
  elaborator caches), with the tests above, the determinism ones ignored
  as SW-1800's is (run by name, about 30 s each)? [rec: yes]
