# SW-2391: reuse across calls, as built

SW-2391, Opus, 8 November 2026. Implements option (b) of
[docs/proposals/reuse-across-calls.md](../proposals/reuse-across-calls.md)
(D3420: an invisible optimisation, no source annotations), with every
required change of the independent review
[SW-2393](SW-2393-reuse-across-calls-review.md). **[measured]** numbers come
from the runs named; **[inferred]** is reasoning.

## In short

A cell taken apart in one function can now be rebuilt in place by another.
Where the bytecode compiler holds a reuse token at a call of a function that
builds a constructor of that size (directly or a few calls down), it calls a
*copy* of the function that takes the token as one more, last, parameter.
dijkstra (2021 day 15) goes from 41.62 G to 37.06 G instructions, **−11.0%**;
`Map.Tree.rebuild` goes from 12.86 M new `Bin` cells to 12.81 M reused ones
**[measured]**. Results, steps, frames, error messages and the native calling
convention are unchanged.

## What was built

- **`crates/rt/src/reuse.rs`**, a pass after `trmc::apply` in `lower.rs`:
  - *wants*: the sizes each function builds, or its callees want, at most
    `DEPTH` = 4 direct calls down;
  - *planning*: the bytecode compiler itself runs over every body in a
    planning mode (`code::plan`) and reports at which calls it would pass a
    token to a function that wants one. Each such (function, size) gets a
    copy, whose body is planned in turn, breadth first, until nothing new
    comes up. So the pass and the compiler can't disagree about where tokens
    are.
  - *caps*: `MAX_COPIES` = 256 per program, and IR growth of at most 25% of
    the program's nodes or 2,000 nodes, whichever is more (a small program
    using `Map` is mostly `Map`: with a plain 25% the test program's
    rotations were capped out).
  - *excluded*: constants, natives, any body using a hole operation (TRMC's
    twins, their `[cells#N]` helper copies and their wrappers), and bodies
    nested beyond `MAX_NESTING`.
  - *the copy's body* is the original's shifted by `trmc::shift` (the tested
    routine TRMC uses for its two extra parameters), so slot `params` is the
    token, which the IR never reads or binds. Named `f[reuse]`
    (`f[reuseN]` when one function has copies of several sizes).
- **`ir.rs`**: `Global.reuse: Reuse` — `None`, `Copies(Vec<(size, copy)>)` on
  the original, or `Copy { of, size }` on the copy.
- **`code.rs`**: a copy's code starts with the token in hand; a call claims a
  token for a copy (marked `MOVE`, appended last); the claim rules below.
- **`validate.rs`**, **`codec.rs`** (format 2), **`linked.rs`** (format 2),
  **`shared.rs`**, **`machine.rs`**: checks, encoding and the depth note.
- **native `n1.rs`**: the empty-token fast path in `ctor_reuse`; no value
  adapter for a copy.

## The review's findings, one by one

| Finding | How it's handled |
|---|---|
| F1 plumbing | `Program::validate` checks that a copy's token slot (its last parameter) is never read or bound, that nothing (`Call`, `Global`, `PartialApp`) names a copy anywhere, and that each copy and its original list each other with matching arities. `code.rs` asserts (a real `assert!`, not only in debug builds, since the tests run in release) that every token claimed, by a constructor or a call, is a register a token was made in. The shift is `trmc::shift`. Tests: `reuse::validation_keeps_tokens_out_of_the_ir`. |
| F2 built executables | The copies are globals of the `Program`, with `Reuse` on each, encoded by the codec (format version 1 → 2) and validated on decode, so `stitchwort build` rebuilds the same bytecode. `--native` executables carry the copies' native code; their outline carries `copy_of` (linked format 1 → 2) for the depth note. Tests: `reuse::copies_survive_the_codec` (same bytecode, the copy called) and `build::native_executables_keep_the_copies_that_reuse_cells` (symbols `…rebuild[reuse]#N` in the executable; same output as `run`, `run --native` and a plain build). |
| F3 shared maps | Native `ctor_reuse` first tests for an empty token (tag 0) and builds the cell inline as `Ctor` does, with nothing to drop. **This is SW-2395's change**, so SW-2395 can be closed. Measured on matcher, the shared case the review named: 81.71 → 81.40 G. The shared-map test checks answers, that the old map reads unchanged, and the machine/native traces. |
| F4 bounds | `DEPTH` = 4, `MAX_COPIES` = 256, growth ≤ max(25%, 2,000 nodes). Counts below. Test: `reuse::copies_stay_within_their_caps_on_aoc`. |
| F5 claim order | Stated in `code.rs`'s module doc and enforced: (1) a token goes to the instruction that claims it, in emission order; a constructor takes any token of its size, innermost first (as before). (2) A call takes one only if more tokens of the size are held than the constructors still to come on its path can use: those of later operands, a `let`'s body, the arms after a scrutinee, and the constructor whose field the call is (`Later` in `code.rs`). (3) A match keeps a token if its arm builds or calls a copy of the size; `DropReuse` makes one if fewer *non-passed* tokens are held than the branch could use, so a passed token never suppresses a local one. Test: `reuse::constructors_take_the_token_before_their_fields` (A/B pair). |
| F6 names | The depth note folds a copy's frames into its original (`Image::folds`, `Outline::folds`): same text as before. Test: `reuse::the_depth_note_counts_copies_as_their_original`. The profiler already folds any `[…]` suffix (`profile.rs` `source_name`), so `[reuse]` copies are in their definition's row (orchestrator's call, as the brief said). `--count-bodies` and `STITCHWORT_NATIVE_DUMP` show copies by their own names. |
| TRMC exclusion | By hole operations in the body. Test: `reuse::loops_get_no_copies`. |
| F7/F8 restated | In the proposal's status paragraph. |

## The soundness argument, as implemented

1. Tokens are still made only by `Unpack` and `DropReuse`, from a cell with a
   count of 1 whose fields were moved out, or are `Erased`.
2. A token lives in a register the IR never names: a temporary, or a copy's
   last parameter, which `validate` proves the body never reads or binds.
3. A token is only moved: into one `CtorReuse`, or as the last operand of one
   call of a copy, marked `MOVE`; or released with its frame. `code.rs`
   removes it from its list when it's claimed, and asserts the register is a
   token's.
4. A copy is never a function value (`validate`), so its last argument is
   always a token passed by the compiler, never a program value. This is
   what keeps native `ctor_reuse`'s fast path (which doesn't drop the old
   fields) agreeing with the machine.
5. `CtorReuse` still checks the cell's size and count at run time, so a
   mistake about *which* calls get a token costs an allocation, never an
   answer.
6. Steps and frames: a call of a copy enters one frame where the original's
   call did; the pass runs after every inlining decision. Allocation traces
   change (more `reuse` events), and the machine and native code agree on
   them (every `same_trace` test).

## Uniqueness on dijkstra (review F7)

Per-site counts from temporary interpreter instrumentation (SW-2371's
method; not committed), `stitchwort run Aoc.Year2021.Day15.main` on the real
input, answers 656 and 2979 both ways **[measured]**:

| Site | Before | After |
|---|---:|---:|
| `Map.Tree.rebuild` `Keep` `Bin` | 12.86 M new | 12.81 M reused (`rebuild[reuse]`) |
| `insertWith.%match1[0][10]` unpacks | 7.15 M + 2.55 M unique | the same, in its copy |
| `insertWith.%match1[0]` unpacks | 1.53 M + 0.75 M unique | the same, in its copy |
| `minView` unpack | 1.67 M unique | the same, in its copy |
| `singleL` second `Bin` | 0.46 M new | 0.46 M reused |
| `doubleL` `Bin` | 0.58 M new | 0.50 M miss on an empty token |
| `insertWith` `Equal` `Bin` | 0.37 M new | 0.37 M reused |

No unpack on an insert or pop path is shared: the cells are unique on
dijkstra itself, not only on the micro-benchmark. The remaining `doubleL`
misses are the review's "every insert, once" case: the new leaf takes the
passed token, so the level above rebuilds into an empty one. That is still
one new node per insert. The shared unpacks left are `Map.Tree.get` and
`shape` reads (16.9 M, 6.5 M, 1.1 M), which aren't rebuilds.

## Benchmarks

`task bench:compare -- --runs 3 --runners native --instructions dijkstra
disk matcher binary-trees memory-game expressions`, before (base 70e86e1b5)
and after, same machine, 8 Nov 2026 **[measured]**:

| Program | Instructions before | After | Change | Time before | After |
|---|---:|---:|---:|---:|---:|
| dijkstra | 41.62 G | 37.06 G | **−11.0%** | 2.88 s | 2.54 s |
| disk | 120.29 G | 118.30 G | −1.7% | 7.82 s | 7.79 s |
| matcher | 81.71 G | 81.40 G | −0.4% | 5.25 s | 5.39 s |
| binary-trees | 30.08 G | 30.08 G | 0 | 1.80 s | 1.59 s |
| memory-game | 33.52 G | 33.52 G | 0 | 2.82 s | 2.73 s |
| expressions | 540.06 G | 537.11 G | −0.5% | 38.63 s | 39.90 s |

Times were taken under load from other lanes; instructions are the number to
read. Native build time of dijkstra: 6.2 s before, 6.3 s after.

## Copies and IR growth

- The test program of the Map tests: 11 copies (`insertWith`'s lifted match
  and its specialisations, `minView`, `rebuild` and the four rotations,
  `popMinRaw`, a caller's match), 601 nodes added to 1,160.
- dijkstra: 15 copies, 807 nodes added to 5,972 (13.5%).
- Every AoC day (71 `main`s, one run of the caps test at the full sample):
  767 copies, 35,502 nodes added to 341,570, **10.4%**; at most 24 copies
  and 1,125 nodes for one day (2024 day 15). No day hit a cap.

## Tests run

- New, `crates/native/tests/it/reuse.rs` (machine and native, traces equal,
  no leaks): Map paths with every rotation (900 inserts, 900 pops: at most
  one new node per operation; before, over 10,000), a shared map, tokens
  held across a closure (`insertWith`'s `f`) and recursion (`minView`), tail
  calls (a copy reached by tail call, a copy's self tail call: 2 new boxes
  against 52), the A/B pair (both ≥ 80.6%; B was 6.9%), early exits at every
  step and frame limit mid-chain (no leak, same stop as the machine), the
  depth note, TRMC exclusion.
- New, `crates/rt/tests/it/reuse.rs`: validation, codec, a handler resuming
  twice (against the reference evaluator), caps on AoC (sampled; all days
  at the full tier's sample).
- New, `crates/cli/tests/running/build.rs`:
  `native_executables_keep_the_copies_that_reuse_cells`.
- `task test:lane AREA=rt`: 64 passed (the new `reuse::` tests added to the
  lane). `task test:lane AREA=native`: 63 passed (includes the machine/native
  agreement tests of `n1.rs`). `task bench:compare:check`: 66 ok, 0 failed (9.6 min, beside another lane's check).
  `cargo fmt`; `cargo clippy --release -p stitchwort-rt -p stitchwort-native
  -p stitchwort-cli --tests -- --deny warnings`, also with
  `--features stitchwort-cli/native`: clean.

## Not done, and open points

- No dedicated shared-map benchmark was timed apart from matcher.
- Closures and `Apply` pass no tokens (direct calls only), as the note said.
- Unspent tokens are held to frame end, as the review expected; not measured
  separately.
- The planning pass compiles each body once more; compile-time cost not
  measured beyond dijkstra's native build time (6.2 → 6.3 s).
