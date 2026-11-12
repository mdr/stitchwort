# SW-2999: what hitting the size limit costs, and what to do about it

Paper lane, 12 Nov 2026, against `main` at `804b1882c`. Nothing was built or run: every
figure here is either **cited** (from the ticket or note named), **inferred** (read from the
code), or **estimated** (worked out from the type definitions, not measured).

It builds on [docs/proposals/term-sharing.md](../proposals/term-sharing.md) (SW-2660, Fable,
10 Nov), which measured the same cost (125 to 215 bytes per node, 1.32 GB for
`rewrite-value-too-large.sw`, 2.23 GB for `rewrite-solution-too-large.sw`) and asked
D3464, "lower the read-back size limit from 10 million nodes to 1 million?". D3464 has no
answer on the board or in the note. This review adds what that note left out: why a node costs
what it does, what smaller nodes would save, what the browser does, and which programs
depend on the limit's value.

## In short

- **The problem.** When something a user writes makes a value that is too big to write out,
  Stitchwort stops, but only after building about 10 million pieces of it. That takes 1.3 to
  2.4 GB and 1 to 2 seconds on the laptop before the error appears (cited, SW-2996 and
  SW-2660). In the playground the same check takes roughly half the memory but keeps it:
  WebAssembly memory never shrinks, so the editor's worker holds that peak until it is
  restarted.
- **The change.** Lower the limit from 10 million nodes to 1 million, after a counter has
  confirmed over the whole corpus that nothing real comes near it. Leave the node layout
  alone.
- **What it should do.** The same error, about ten times sooner and smaller: about 0.13 to
  0.24 GB and 0.1 to 0.2 s instead of 1.3 to 2.4 GB and 1 to 2 s (estimated, by scaling the
  measured cases). The largest term any real declaration ends up as is 106,000 nodes
  (measured by SW-2660), so 1 million leaves about 10× headroom. The five heavy reject
  examples could go back into the merge tier's sample.

## 1. What a node is and how it's counted

**Where.** `Limits::size` (`crates/core/src/budget.rs:93`, set to 10,000,000 at `:122`) is read
in exactly two places, both through `Budget::size_limit` (`budget.rs:640`):

- `quote_as` (`crates/core/src/value.rs:3049`), the one read-back behind `quote`,
  `quote_folded`, `quote_as_written` and the display variants. It counts a node **each time
  it visits a value** (`size += 1`, `value.rs:3079`), before building anything for it, and
  fails with `ResourceError::Size` once the count passes the limit (`value.rs:3083`).
- `rename` (`crates/elab/src/unify.rs:2606`), which writes a unification solution as a term:
  the same count per value visited (`unify.rs:2648`, SW-2409).

So a "node" is one value visited during **one** read-back. It is not counted at evaluation,
and it is not a total for the check: each read-back starts from zero. Evaluation itself is
bounded by steps and frames, not size. A value of 31 cells (`grow 30 (Leaf x)`, its subtrees
shared) is 2^31 nodes, because read-back writes shared parts out once per use
(term-sharing.md §2.1).

**What gets built per node** (inferred from `quote_as`, `value.rs:3057` to `3130`): each
visit pushes either a finished leaf term or an assembly task. Children finish onto a stack
`done: Vec<Term>`. An assembly pops its parts into a temporary `Vec<Term>` (`split_off`,
`value.rs:3098`, `:3102`, `:3121`) and wraps each part in its own `Rc` (`Term::ctor`,
`crates/core/src/term.rs:390`). So nearly every counted node ends up as one `Rc<Term>`
allocation, and every constructor, data type or quotient node also gets a separate heap
buffer for its `Vec<Rc<Term>>` of children. When the limit trips, everything built so far is
live, in `done`, and is freed only as the error unwinds.

## 2. Why a node costs 125 to 215 bytes

**The term node (estimated, 64-bit).** `Term` (`term.rs:161` to `228`) is sized by its
largest variants: `Ctor(DataId, usize, Vec<Rc<Term>>)` is 8 + 8 + 24 = 40 bytes, and
`Let(Name, Rc, Rc, Rc, bool)`, with `Name = Rc<str>` a 16-byte fat pointer (`term.rs:12`), is
41 bytes. With the tag, `size_of::<Term>()` is 48. In an `Rc` it gains two 8-byte counts:
**64 bytes per node**, exactly one of mimalloc's size classes. A constructor's child list adds
a buffer of 8 bytes per child (16 for a binary node).

**Worked out for `grow 30 (Leaf x)`** (`examples/reject/rewrite-value-too-large.sw`): each
leaf of the tree is three counted nodes, a `Node`, a `Leaf` and the variable `x`. Their
allocations are 64 + 16, 64 + 8, and 64 bytes: 216 bytes for three nodes, **about 72 bytes per
node**. At the limit, about 0.72 GB.

**Measured, 124 bytes per node** for that file (SW-2660: 1.32 GB peak, less the 80 MB an
empty file takes, over 10 million nodes). So the term tree explains a bit over half. The rest
is not visible from the code alone. The candidates, each **inferred**, none measured:

- **The work stacks, on deep values.** `tasks` holds about 72 to 80 bytes per entry
  (`QuoteTask::Visit` carries a whole `Value`, 56 bytes, plus two `usize`s; `value.rs:3152`)
  and `done` holds 48 bytes per entry. For a balanced tree like `grow`'s these stay as small
  as the tree is deep. For a right-leaning chain (nested `if`s, long lists: the three
  `as-written-unconfirmed-*` examples) nothing is assembled until the end, so both stacks hold
  one entry per level. That's about 120 bytes a level, and with `Vec` doubling up to twice
  that, three times during a reallocation.
- **More than one read-back reaching the limit in one check.** `rewrite` falls back to the
  as-written search after the usual one runs out (`crates/elab/src/rewrite.rs:1011`), and
  the unifier can try `rename` after a read-back. They run one after another, so their peaks
  shouldn't add, but freed memory in a different size class isn't necessarily reused.
- **`rename` builds terms recursively** (`unify.rs:2606` onwards), collecting each node's
  children into a `Vec` before wrapping them. That would fit `rewrite-solution-too-large.sw`
  costing more per node (2.23 GB, about 215 bytes) than `rewrite-value-too-large.sw`.

The values themselves cost almost nothing here: they are shared (a `Values` is one
`Rc<[Value]>`, `value.rs:613`; a call's unfolding is memoised in its `Rc<Unfolding>`,
`value.rs:263`), so the cost is all in the writing out.

**In the browser (estimated).** `wasm32` has 4-byte pointers. `Term` comes to about 24 bytes
and an `Rc<Term>` with dlmalloc's chunk header to about 40, so each node costs a little over
half the native figure: roughly 0.6 to 1.1 GB at the 10M limit. The playground uses the same
10M limit (`session_limits`, `crates/web/src/lib.rs:43`). Nothing sets a maximum for the
module's memory: `crates/web/build.rs` and `.cargo/config.toml:5` set only the stack. So the
ceiling is the engine's, 4 GiB in desktop Chrome and Firefox (lower on phones; not checked).
So the tab probably survives one such check on a desktop. But WebAssembly memory only grows,
so the worker keeps that peak for the rest of the session. If an allocation does fail, Rust
aborts, the worker reports `crashed` (`web/lsp-worker.js:171`), and the editor restarts it and
reopens the same document (`web/editor/src/editor-entry.js:233`). That happens up to three
times, and then the language server stops with "The language server crashed". The user
gets no `E-RESOURCE`.

## 3. Who depends on the limit's value

- **The check cache.** `options.limits.size` is part of every cache key
  (`crates/elab/src/state/options.rs:156`), so changing it misses every cache once
  (migration cost, which doesn't count, D2303).
- **Smaller limits already in use**, all lower than 10M and none reported as refusing real
  code: tried proofs in `search --at` 200,000 (`TRIED_PROOF_SIZE`,
  `crates/elab/src/lib.rs:740`, applied at `:1132`); search 100,000
  (`crates/elab/src/search.rs:44`); equation generation 1,000,000
  (`crates/elab/src/equations.rs:106`); `assume` 50,000 (`crates/elab/src/assume.rs:63`);
  the elab fuzzer 1,000,000 (`crates/driver/tests/fuzz_elab.rs:79`, SW-2582); `omega` and
  `ring` 10,000; display caps 200,000 (`crates/elab/src/check.rs:313`).
- **Tests that pin it.** None pins 10M itself. `crates/elab/src/kernel.rs:296` checks that a
  size limit (12,345) survives a reset. `crates/driver/tests/resources.rs` sets its own small
  limits.
- **Examples whose outcome rests on running out.** The five heavy reject examples
  (`HEAVY`, `crates/cli/tests/running/examples.rs:141`) expect `E-RESOURCE` or a mismatch
  reached after the usual search ran out. A lower limit gives the same outcome sooner.
  `examples/accept/as-written-unconfirmed.sw` relies on the unfolded read-back of
  `settle x k 3000` running out, so that `match` and `rewrite` fall back to the goal as
  written, with `W-MATCH-UNCONFIRMED` and `W-REWRITE-UNCONFIRMED`. A lower limit only makes
  the fallback come sooner (D2543: limits fail, never choose). AoC 2020 day 11, the shape that
  example comes from, keeps `roundLimit` a parameter in its proofs
  (`aoc/src/Aoc/Year2020/Day11/Proofs/Parts.sw:63`), so it never unfolds 1,000 rounds.
- **Real code** (cited, SW-2660 §2.4): the largest term any declaration ends up as in all of
  std, seven heavy AoC namespaces and `Rogue.Proofs` is 105,898 nodes. The largest single
  read-back has never been measured, because no counter exists (SW-2681). The only real
  project known to have reached 10M is trip-journal on the record-eta branch, in 33
  declarations, all of them failures.

## 4. Options, judged by the end state

| Option | Saves at the limit | Risk to real code | Work | Verdict |
|---|---|---|---|---|
| **(a) Limit 1M nodes** | ~10×: 0.13-0.24 GB, 0.1-0.2 s (estimated) | A real read-back between 1M and 10M would become `E-RESOURCE`; none known (largest term 106k) | Counter (SW-2681), one corpus run, a constant, snapshots | **Do it** |
| (a′) Limit 250k-500k | 20-40× | Headroom only 2.5-5× over the largest term | Same | Not yet; revisit with the counter's data |
| (b) Smaller nodes | ~30% (estimated: `Term` 48 → 32 bytes by interning `Name`s to `u32`, `u32` ids, `Rc<[_]>` children, boxing `Let`; `grow`'s 72 B/node → ~50) | None | `Term` is matched or built at about 480 places in 56 files (SW-2660); every hash and pass touched | No: a third of the gain of (a) at many times the cost; worth it only for its own sake |
| (b′) Leaner work stacks | Up to ~half of the per-node cost on deep chains (estimated); nothing on balanced trees | None | `quote_as` only: a `Visit` holding `&Value` or an index, `done` pre-sized | Small; fold into (a)'s lane only if the counter shows deep-chain cases dominate |
| (c) Byte budget per check (allocator counter) | Bounds *every* runaway, not just read-back | Bytes differ by build (wasm vs native), so a check near the cap can pass in one and fail in the other | Opus lane for the mechanism (`budget.rs`'s existing cancel poll + heap_cap.rs made a product feature), Sonnet lane for CLI/LSP/web | A good backstop, already proposed (term-sharing.md §4, "Question 2"), but not what this ticket needs: the size limit is deterministic and is what users should meet first |
| (d1) Measure before building: count a value's tree size with a memo keyed by `Rc` address, fail before allocating | Group A (shared values) ends at near-zero memory | Values under binders are re-evaluated on each visit, so it can't see through closures; two counts to keep in step | Medium, in `quote_as` and `rename` | Not now: covers the 3 of ~15 incidents that come from sharing (term-sharing.md §1) |
| (d2) Sharing in terms (DAGs, hash-consing) | Group A becomes fast, not an error | Memos in the kernel | 3-5 weeks (SW-2660) | No (term-sharing.md §3) |
| (d3) A browser-only lower limit | Protects the worker's memory | The cache bundle is built by the WebAssembly build itself, so it's consistent; but answers would differ by host | A constant | Unnecessary once (a) is done: 1M nodes is ~60-110 MB there (estimated) |

## 5. Recommendation

**Lower `Limits::size` to 1,000,000 nodes, everywhere, after a counter confirms the
headroom.** This is D3464 from term-sharing.md, which nobody answered. The analysis here
supports it.

- Native, at the limit: from 1.3 to 2.4 GB and 1 to 2 s down to about 0.13 to 0.24 GB and
  0.1 to 0.2 s (estimated, linear in nodes since the term is built node by node).
- Browser: from roughly 0.6 to 1.1 GB, kept by the worker for good, down to about 60 to
  110 MB (estimated).
- Tests: the five `HEAVY` examples drop to about 0.2 GB each, so `HEAVY` and
  `skips_heavy` can go and the merge tier samples them again.

**What a lane builds (two lanes, Sonnet; estimated 45 + 60 min):**

1. **The counter** (SW-2681, bounded read-back stage 0c): the largest node count of any one
   read-back or `rename` per declaration, kept on `Budget` beside `too_large` and printed
   with `STITCHWORT_TIMINGS=decls`. Then the orchestrator has the verifier or Overmind run it
   over std, all of `aoc/`, `games/rogue` and the examples. This is a whole-corpus run, which
   a lane must not do. If any real read-back is over 250,000 nodes, the number is looked at
   again before step 2.
2. **The change**: `size: 1_000_000` in `Limits::for_stack` (`budget.rs:122`). Update the
   field's doc and the `HEAVY` comment, then remove `HEAVY` and `skips_heavy` from
   `crates/cli/tests/running/examples.rs`. Re-snapshot the reject examples whose messages
   move. Add the limit to the message (SW-2682: "a value was too large to write out (over
   1,000,000 parts)", since "to show" is wrong for a `rewrite`; the wording is Matt's, under
   D3536 below). Measure the five examples' peaks with `/usr/bin/time -l`, one at a time and
   by name, to confirm the estimate. The `docs/testing.md`
   "Memory" note on `HEAVY` then goes too.

Not recommended now: smaller nodes (b), which save about a third for a large sweep, and
sharing (d1, d2). The memory budget (c) remains a separate open question in term-sharing.md
(its "Question 2"). It is the only thing that also bounds the incidents that aren't
read-backs, and this review doesn't change that case.

## D3536

**D3536: lower the read-back size limit from 10 million nodes to 1 million, everywhere (the
CLI, the editor and the playground), once a counter run over the whole corpus shows no real
read-back above 250,000 nodes?** This answers term-sharing.md's D3464 too. A user who writes
something that blows up gets the same `E-RESOURCE`, but after about 0.2 GB and a fifth of a
second instead of about 2 GB and 2 seconds. In the playground the editor's worker no longer
keeps up to a gigabyte for the rest of the session. The message names the limit: "a value was
too large to write out (over 1,000,000 parts)". The risk is that a valid program needing a
read-back between 1 and 10 million nodes is refused. None is known, since the largest term
measured is 106,000, and the counter run comes first. **[rec: yes]**
