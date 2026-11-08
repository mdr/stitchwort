# SW-2363: a per-run cell cache in native code (trial)

8 November 2026, Opus lane. The trial Matt asked for in D3413 ("try it out.
We'll measure the improvement and we'll see if the extra complexity
justifies the performance gain"). The design is option C of
[cell-allocator.md](../proposals/cell-allocator.md) (SW-2360). Branch
`lane/SW-2363`.

## In short

- **binary-trees:** 30% fewer instructions, and about 10% less time
  (1.54 s to 1.38 s, measured). The design estimated 25–35% less time. The
  instruction count fell as much as estimated, but the time didn't.
- **The other nine programs:** 0–2.5% fewer instructions. Their times
  moved by less than the noise (within ±2%).
- **Memory:** peak memory is the same (+0.05%).
- **Code added:** about 225 lines of code (115 in the new module, 71 in the
  code generator, 38 elsewhere) and one new runtime helper, plus tests.
- **My recommendation:** keep it, narrowly. See "Recommendation" at the
  end.

## What was built

- **The lists.** `crates/rt/src/cell_cache.rs` holds `CellCache`. It has one
  list of freed cells for each cell size from 1 to 8 fields, and a `room`
  word. The lists are linked through each freed block's strong-count word.
- **Where the cache lives.** The `NativeExecutor` owns it. Each crossing
  into native code takes it into its `Context` and hands it back at the
  end (`lend` in `Crossing::context`, and back in `Crossing::finish`). So
  the cache lasts the whole run, across IO steps. Dropping it frees every
  block it holds. That happens when the run ends, whatever the result, and
  as soon as a crossing fails (out of steps, out of frames).
- **New cells.** In the generated code (`n1.rs`), `new_cell` takes the
  first block of the right size: one load, a branch, one load of the next
  block, one store of the new head, and a store of the count. It calls
  `sw_cell_new` only when that list is empty.
- **Freed cells.** `Unpack`'s emptied-cell path pushes the cell onto its
  list: one load of the room, a compare, one load of the head, three
  stores. It calls into the runtime only when the room has run out.
- **The cap.** 64 MB. Taking a block doesn't give its room back. A version
  that did cost binary-trees about 5% of its time: 1.45 s against 1.34 s
  with no cap at all. The cost came from the extra load and store of the
  same context word on every take and every return. So `room` is a lower
  bound on what's really free. When it runs out, the new helper
  `sw_cell_cache_full` counts the lists again. If they hold more than half
  the cap, it cuts them to half and frees the rest. Then it keeps the cell.
  On binary-trees this recount runs 116 times in the whole run; on matcher,
  12 times.
- **Traces.** Code compiled with `trace_refcounts` never uses the cache.
  While an allocation trace may be recording, untraced code is lent an
  empty cache with no room. Every return then goes through
  `sw_cell_cache_full`, which hands it to `sw_cell_free`, so every trace
  sees every allocation and free. The existing tests compare untraced
  code's trace with the machine's too: 19 of them failed until this was in
  place.
- **The switch.** `cell_cache::ENABLED`. Off, the generated code is as it
  was before. Measured with the switch off: binary-trees ran 30.16 G
  instructions, against 30.08 G before the change.

**Touch points outside the module:**

| File | Change |
|---|---|
| `native_abi.rs` | `Context.cells` and `CELLS_AT`; `NativeRun.cells`; `NativeExecutor.cells`; lent in `context`, returned in `finish`, reset when a crossing fails; `sw_cell_free`'s body moved into `free_emptied` (shared with the cache); `sw_cell_cache_full` |
| `n1.rs` | `new_cell`'s take, `Unpack`'s return, the helper's registration (3 lines) |
| `alloc_trace.rs` | `recording()` |
| `call_counts.rs` | one entry for the new helper |

**Removing it:** delete the module, the `Context`, `NativeRun` and
`NativeExecutor` fields, the two lines in `context` and `finish`, the new
helper, and `n1.rs`'s two branches. Or turn `ENABLED` off.

## Why it's safe

- **A block is either cached or live, never both.** A block goes into the
  cache in one place only: `Unpack`'s path for a unique cell (strong and
  weak counts 1) whose fields have all been moved out. That cell would
  otherwise be freed there. It leaves the cache in one place only: it's
  popped off its list and handed out as a new cell.
- **Rust drops never touch the cache.** A cell freed by a Rust drop, the
  machine or a helper goes to the global allocator, as before.
- **A handed-out block is an ordinary `Rc`.** It's an `Rc<[Value]>`
  allocation of exactly that many fields that was never deallocated. Its
  weak count stayed 1 while it was cached, and its strong count is set
  back to 1 when it's taken. So any Rust drop can free it later, through
  any global allocator.
- **New cells are filled before use.** Native code writes every field
  before the cell is read, exactly as it does a cell from `sw_cell_new`.
- **Freeing a cached block** goes through the same code as `sw_cell_free`:
  an `Rc` of `MaybeUninit` fields, so no field is dropped.
- **Threads.** The executor isn't `Send`, and each crossing has its own
  `Context`. No synchronisation is needed.
- **Runs.** Cached blocks never leave their executor, and the executor
  frees them when it's dropped.
- **Nested crossings.** The runner doesn't nest them. If one ever did, the
  inner crossing would be lent an empty cache. Handing it back would drop,
  and so free, the cache it replaces. No block is lost.

**Tests of this:**

- A new test, `crates/native/tests/cell_cache.rs`. It's its own binary, with
  a counting allocator. Runs that cache cells and then end normally, out of
  steps, out of frames, or by `Fail` all free every byte they allocated. I
  checked that it catches a leak by breaking the drain: it then reports
  32,576 bytes left behind.
- A unit test of the recount and the cut to half the cap
  (`cell_cache::tests`).
- All of `task test:lane AREA=native`: n1's allocation traces, both traced
  and untraced, n2b, n3, n4, reuse and s6.
- All of `task test:lane AREA=rt`.
- `task bench:compare:check`: every program gives its expected answer.

## Measurements

The machine: Speedwell, M-series. SW-2337 was running at the same time, so
loads ranged from 1.3 to 12. Instructions are the reliable figure.
Before: `121e3143a`. After: the lane's last commit.

**`task bench:compare -- --runs 5 --runners native --instructions`**

| Program | instr. before | instr. after | change | time before | time after |
|---|---:|---:|---:|---:|---:|
| pidigits | 13.37 G | 13.37 G | 0.0% | 1.12 s | 1.09 s |
| binary-trees | 30.06 G | 20.90 G | **−30.5%** | 1.59 s | 1.37 s |
| memory-game | 33.50 G | 33.51 G | 0.0% | 2.69 s | 2.48 s |
| dijkstra | 18.74 G | 18.25 G | −2.6% | 1.23 s | 1.22 s |
| octopus | 27.58 G | 27.62 G | +0.1% | 1.50 s | 1.50 s |
| disk | 107.14 G | 104.79 G | −2.2% | 7.01 s | 6.78 s |
| expressions | 334.71 G | 327.62 G | −2.1% | 23.44 s | 23.52 s |
| scan | 340.65 G | 332.94 G | −2.3% | 25.27 s | 24.88 s |
| matcher | 71.46 G | 69.80 G | −2.3% | 4.65 s | 4.63 s |
| bridge | 113.97 G | 111.16 G | −2.5% | 7.79 s | 7.67 s |

The bench's times were taken at different moments, so they carry the
other lane's load. Matched before/after pairs, run one after the other
with `hyperfine -N`, are fairer:

| Program | before | after | change | load |
|---|---:|---:|---:|---|
| binary-trees (10 runs × 2 pairs) | 1.539 s, 1.549 s | 1.377 s, 1.373 s | **−10.6%** | ~1.3 |
| binary-trees, again later | 1.561 s | 1.418 s, 1.434 s | −8.6% | 2.5–12 |
| matcher (6 runs × 2 pairs, first version) | 4.531 s, 4.537 s | 4.632 s, 4.584 s | +1.6% | ~2.5 |
| matcher, final version (minimum of 6) | 4.654 s, 4.671 s | 4.605 s, 4.539 s | −2% | up to 12, noisy |
| dijkstra (first version) | 1.187 s | 1.175 s | −1.0% | |
| disk (first version) | 6.79 s, 6.82 s | 6.74 s, 6.98 s | noise | |

**The three versions on binary-trees** (`hyperfine`, same load):

| Version | instructions | time |
|---|---:|---:|
| before | 30.08 G | 1.539 s |
| room given back on every take | 21.13 G | 1.454 s |
| no cap at all (an experiment, not kept) | 20.44 G | 1.339 s |
| room only taken, counted again when it runs out (kept) | 20.92 G | 1.377 s |

**Peak memory** (`/usr/bin/time -l`, peak memory footprint):

| Program | before | after |
|---|---:|---:|
| binary-trees | 69.22 MB | 69.26 MB |
| matcher | 58.29 MB | 58.31 MB |

**How often the cache is used.** These are the call counts of a
`call-counts` runtime, with the switch on and off.

| Program | cells made | from the cache | cells freed by native code | into the cache | recounts |
|---|---:|---:|---:|---:|---:|
| binary-trees | 68.33 M | 67.28 M (98.5%) | 67.81 M | 67.81 M (100%) | 116 |
| matcher | 34.45 M | 17.54 M (50.9%) | 17.54 M | 17.54 M (100%) | 12 |

matcher's other cells (31.8 M `sw_drop_words`) are freed by Rust drops.
The cache doesn't see those (that would be stage 3 of the design).

## Why the time fell by less than the estimate

The estimate came from the allocator's share of the profile (about 45% of
binary-trees' samples), and that share was not all removable time.

After the change, the allocator is 1.1% of binary-trees' profile, and
generated code is 98.3% (`task profile:native -- binary-trees`). So the
allocator's instructions are gone. But the generated code now takes about
1.35 s, where before it took about 0.9 s.

The instructions that went were mimalloc's fast path. That path runs at a
high instruction rate: before the change, the run retired about 19.6 G
instructions a second; after it, 14.6 G. What remains is the generated
code's own chains of dependent loads and stores. Those now set the pace.
This is inferred from the two profiles and the rates, not measured with
hardware counters.

The lesson for later estimates: a function's share of a profile isn't the
time saved by removing it, when it runs alongside slow chains of loads.

## Recommendation

Keep it, narrowly.

**For keeping it:**

- binary-trees is a headline comparison program, and it gets 10% faster.
- No program got slower.
- Peak memory didn't change.
- It's one module, and the generated-code side is two short branches.
- It's the shape compact values (SW-2324) needs anyway for its own free
  path (design option E). That lane could absorb it.

**Against keeping it:**

- The gain is on one program. Elsewhere it's 2% of instructions and no
  time that can be seen.
- It adds about 225 lines of unsafe-adjacent code, a helper, and a second
  route by which cells are freed. Anyone changing the cell layout must keep
  that route in mind.

**If Matt drops it:** revert the two commits. The tests that would go with
them are the new ones only.

## Not done

- **Stage 3 of the design** (Rust drops into the cache) and closures. Both
  are out of scope.
- **matcher's time.** Its time gain under load isn't settled: −2% to +1.6%
  across two versions, against 2.3% fewer instructions. A quiet machine
  would settle it.
- **No `task profile:native` before the change** for this lane. The "before"
  profile is SW-2321's.

## Worth filing

- **The profile estimate gap.** This could be a note in
  docs/proposals/lean-runtime-speed.md: an allocator's self-time share overstates what removing it
  saves.
- **A per-op counter in `Context` costs about 5% on allocation-heavy
  code.** That's the load and store of the same word on the critical
  path. It's worth knowing before any other inline counter is added (a
  `deferred`-style count on a hot path).
- **The shared scratchpad.** This session's lanes share one scratchpad
  directory. SW-2337 and this lane both wrote `before.txt` there, and a
  baseline was nearly mixed up. Lane briefs could say to use a
  subdirectory named after the ticket.
