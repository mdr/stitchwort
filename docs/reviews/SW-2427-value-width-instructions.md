# SW-2427: the instructions that exist because a value is three words (compact values, step V2)

Step V2 of [`docs/proposals/compact-values.md`](../proposals/compact-values.md) (§5): on the decision set's native executables, plus scan, which retired instructions move a value's second or third word, spill or reload, save callee-saved registers or test the weak count, and what options C, E and A would leave of them. Also SW-2432: why expressions and scan run at a lower IPC than Lean.

Measured on Overmind (i7-6700HQ, Skylake) on 8 Nov 2026, 19:58 to 20:19 GMT, on `2cfe058ea`. No product code changed.

## The reading

**Go/no-go: value-width work is over 5% on the decision set's mean**, so the refactor can reach the threshold. By the note's rules:

| | mean over the decision set | without binary-trees | binary-trees | note's estimate |
|---|---:|---:|---:|---|
| A removes | **13.1%** | 11.6% | 20.6% | 8–15% (15–25% on binary-trees) |
| E removes | **7.0%** | 6.1% | 11.5% | |
| C removes | 0.7% | 0.4% | 2.2% | |
| A, with register moves (my addition) | 16.9% | 14.1% | 30.6% | |
| E, with register moves (my addition) | 8.9% | 7.3% | 16.5% | |

- These are shares of **all** native instructions retired, runtime and allocator included, removed from generated code.
- A falls inside the note's estimate, on the mean and on binary-trees. E alone is just under it (7.0% against 8–15%), but above the 5% threshold.
- **The runtime side adds at most** 4.3% (E) or 8.5% (A) on the mean. That's an upper bound: a third, or two thirds, of every memory and stack access in the drop walk, the apply stubs and `Value::clone`, as if every one moved a value word. See "The runtime side".
- **Most of the saving is in spills and stack traffic, not in loads of word 1 and 2.** Explicit word 1 and word 2 loads and stores are only 0.5–3% of instructions. Stack traffic (12–15%) and callee-saved saves (2–9%) are where three-word registers cost, and the note's rule credits E with a third of those and A, by my rule, two thirds. So the result rests on that rule. A sharper test would be E's register count itself, which only building E answers.

**SW-2432: expressions' and scan's low IPC is backend core-bound, from store traffic.** It isn't the front end, memory or branch misprediction:
- **Store buffer full:** 5.9% of native cycles on expressions and 6.2% on scan, against 0.05% and 0.09% for Lean.
- **Blocked store-to-load forwarding:** 10.6 per 1000 instructions on expressions and 11.2 on scan, against 0.27 and 0.06 for Lean.
- Both are concentrated in `stitchwort_rt::value::free`, `sw_apply_prepare` and `sw_closure`, the runtime's copying and freeing of 24-byte values. See the SW-2432 section.

## Generated code, by class

Each cell is a share of the program's **total** retired instructions; the "generated code" column is the share in compiled bodies. The classes are described under "How each instruction was classified".

| Program | generated code | word 1 | word 2 | stack | callee-saved | weak count | register moves | context | word 0 | other |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| binary-trees | 97.8% | 1.0% | 1.3% | 15.2% | 8.9% | 2.2% | 15.1% | 6.7% | 1.5% | 45.8% |
| matcher | 48.3% | 0.6% | 1.5% | 13.9% | 2.3% | 0.1% | 4.2% | 1.5% | 1.1% | 23.0% |
| dijkstra | 53.7% | 1.3% | 1.4% | 15.3% | 2.0% | 0.4% | 4.5% | 1.0% | 1.8% | 26.0% |
| octopus | 50.3% | 1.8% | 1.5% | 13.2% | 2.1% | 0.4% | 4.8% | 0.5% | 1.1% | 24.9% |
| memory-game | 52.1% | 1.4% | 1.7% | 12.1% | 1.6% | 0.7% | 4.5% | 0.1% | 0.6% | 29.4% |
| expressions | 9.8% | 0.3% | 0.3% | 3.1% | 1.1% | 0.0% | 0.6% | 0.2% | 0.4% | 3.7% |
| scan | 9.5% | 0.2% | 0.4% | 3.1% | 1.0% | 0.0% | 0.5% | 0.3% | 0.5% | 3.4% |

The runtime side, by group, as shares of the total. The last two columns are the memory and stack accesses within the drop walk, the apply stubs and `Value::clone`.

| Program | drop walk | apply stubs | Value::clone | allocator | other runtime | their memory accesses (drop, apply, clone) | their stack accesses |
|---|---:|---:|---:|---:|---:|---:|---:|
| binary-trees | 0.7% | 0.0% | 0.0% | 0.4% | 1.2% | 0.1% | 0.1% |
| matcher | 18.5% | 7.9% | 0.3% | 8.8% | 16.2% | 5.4% | 8.6% |
| dijkstra | 20.4% | 7.1% | 0.5% | 7.9% | 10.4% | 5.9% | 8.9% |
| octopus | 25.1% | 1.6% | 1.3% | 11.7% | 10.0% | 6.8% | 4.3% |
| memory-game | 25.2% | 0.0% | 0.0% | 13.7% | 9.0% | 7.2% | 4.0% |
| expressions | 32.8% | 14.1% | 0.6% | 13.3% | 29.4% | 9.6% | 15.6% |
| scan | 33.0% | 17.0% | 0.7% | 11.0% | 28.8% | 9.8% | 18.1% |

## What C, E and A remove

The rules are the note's (§5, V2), with my departures listed below. All figures are shares of total instructions.
- "listed classes" is word 1 + word 2 + stack + callee-saved + weak count in generated code: the gross, before any rule.
- C removes the weak count.
- E removes word 2, a third of stack traffic and callee-saved saves, and the weak count.
- A removes words 1 and 2, two thirds of stack traffic and saves, and the weak count.
- "with register moves" adds a third (E) or two thirds (A) of register-to-register moves.
- "runtime bound" is a third (E) or two thirds (A) of the drop walk's, apply stubs' and `Value::clone`'s memory and stack accesses: an upper bound, not an estimate.

| Program | listed classes (generated) | C removes | E removes | A removes | E with register moves | A with register moves | runtime bound E | runtime bound A |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| binary-trees * | 28.6% | 2.2% | 11.5% | 20.6% | 16.5% | 30.6% | 0.1% | 0.2% |
| matcher * | 18.4% | 0.1% | 7.0% | 13.0% | 8.4% | 15.8% | 4.7% | 9.3% |
| dijkstra * | 20.5% | 0.4% | 7.6% | 14.7% | 9.1% | 17.7% | 4.9% | 9.9% |
| octopus * | 19.1% | 0.4% | 7.0% | 14.0% | 8.6% | 17.2% | 3.7% | 7.4% |
| memory-game * | 17.5% | 0.7% | 7.0% | 12.9% | 8.5% | 16.0% | 3.7% | 7.5% |
| expressions * | 4.9% | 0.0% | 1.8% | 3.5% | 2.0% | 3.9% | 8.4% | 16.8% |
| scan | 4.8% | 0.0% | 1.8% | 3.4% | 2.0% | 3.7% | 9.3% | 18.6% |

`*` marks the decision set; means are arithmetic over its six programs.

### Departures from the note's rules

1. **A's spills and saves:** the note gives E "about a third" and no figure for A. I took two thirds: one register of three where E keeps two.
2. **Register moves:** the note doesn't name them. Register-to-register `mov`s are 15% of binary-trees and 4–5% of the AoC programs, and many are a three-word value's words shuffled between registers. I report them as an extra column, scaled like spills, and leave them out of the go/no-go.
3. **The weak count:** only the load of the weak-count word is counted. Its compare is usually folded into the uniqueness test's other instructions (`cmp`, `sete`, `and`) and lands in "other". So C's figure is a lower bound, perhaps half the truth.
4. **A's decoding:** A must decode a scalar where a kind is tested (a shift or mask). The note says "except where a scalar must be decoded"; I didn't add those instructions back, so A's figure is a little high.
5. **The runtime side** isn't classified word by word; see "The runtime side".

## How it was measured

- **Builds:** each program was built with `stitchwort build --native --pc-map` (the same code, plus `NAME.pcmap.json`: each body's stretches of machine code by bytecode instruction and part, SW-2332).
- **Recording:** each run was recorded with `perf record -e instructions:upp -c 100003`: precise, user space, one sample per 100,003 retired instructions. That's 196 k samples (dijkstra) to 3.4 M (expressions). Every run printed the expected answer.
- **Totals:** the samples × 100,003 match the instruction counts measured in SW-2426, within a few percent.
- **Decoding:** the instruction at each sampled address was decoded with `objdump -M intel`. A linear pass decoded most; the inline jump tables Cranelift emits throw a linear pass out of step, so the rest were decoded one by one from their own address. 1 to 249 samples per program stayed undecoded, under 0.01%.

### How each instruction was classified

For a sampled address in a compiled body (a `--pc-map` symbol), the part comes from the map and the class from the instruction:

- **callee-saved:** in the `prologue` or `return` part, a `push` or `pop` of `rbx`, `rbp` or `r12`–`r15`, or a `mov` between one of them and a stack slot.
- **stack (spill/reload/buffer):** any other memory operand based on `rsp` or `rbp`. This is Cranelift's spills and reloads, and also the explicit stack slots that hold values passed to runtime helpers (argument buffers), which can't be told apart from the instruction. Both scale with value width.
- **context:** a memory operand whose base register holds the run's `Context`: the step counter, the frame limit and the cell-cache heads, read in `check` and in the cell cache's inline take and push.
  - A base register is taken to hold the `Context` if its last write before the instruction, in address order within the body, reloads the stack slot the prologue saved `rdi` (the first argument) to, or if it is `rdi` with no write before it.
  - Without this, these accesses landed in "word 1" and "word 2", about 7% of binary-trees.
- **weak count:** a load or compare at `[reg+0x8]`. A cell's counts are at 0 (strong) and 8 (weak), and its fields from 16.
- **word 0, word 1, word 2:** any other memory operand `[reg+disp]` with `disp` ≥ 16, the word being `((disp − 16) mod 24) / 8`: a field's three words at 16 + 24i, 24 + 24i and 32 + 24i.
  - This is right for cells. It misreads values held in other heap objects (array elements, effect records, closures' captures), so word 1 and word 2 are approximate. They're small either way.
- **register move:** a `mov` between two general registers.
- **other:** everything else: arithmetic, compares, branches, calls, constants, word 0's tests and the strong count.

### The runtime side

Rust's code addresses a value relative to many different bases: a `Value` in a `Vec`, a field in an `Rc`'s allocation after its 16-byte header, a closure's captures. So the word of a load can't be read from its displacement, as it can in generated code. I grouped the runtime's samples by function (demangled symbols):
- **drop walk:** `value::free`, the `Value`, `Fun` and `Vec<Value>` drop glue, `Fields::drop`, `Rc::drop_slow`, `take_children` and `sw_drop_words`.
- **apply stubs:** `sw_apply*` and `apply1`–`apply4`.
- **`Value::clone`**.
- **the allocator:** mimalloc and `memcpy`/`memmove`.
- **other runtime:** the rest, mostly the effect runtime: `sw_eff_step`, `rt_loop`, `sw_bind` and `sw_closure`.

Within the first three, I counted memory and stack accesses. The bound assumes every one moves a value word and that E removes a third of them and A two thirds. The drop walk tests each field's kind and frees through its pointer: it reads words 0 and 1, rarely word 2. So the real saving is likely well under the bound for E, which removes only word 2.

## SW-2432: the parsers' low IPC

expressions and scan, native against Lean. Native figures are from the `--pc-map` builds; Lean's from `bench/compare/lean`.

| | expressions native | expressions Lean | scan native | scan Lean |
|---|---:|---:|---:|---:|
| IPC | 2.00 | 2.66 | 2.12 | 2.94 |
| top-down retiring | 51.8% | 63.5% | 55.2% | 70.5% |
| frontend-bound | 24.2% | 28.7% | 21.5% | 25.3% |
| bad speculation | 6.5% | 4.9% | 5.3% | 2.1% |
| backend-bound | 17.5% | 2.9% | 18.0% | 2.1% |
| memory-stall share of cycles (SW-2426) | 8.5% | 6.4% | 6.7% | 4.7% |
| branch misses per 1000 instructions | 1.03 | | 0.73 | |
| L1i misses per 1000 instructions | 28.7 | | 31.3 | |
| iTLB misses per 1000 instructions | 0.004 | | 0.002 | |
| µops from the decoded-µop cache (DSB) | 22% | | 25% | |
| **store buffer full** (`resource_stalls.sb`), share of cycles | **5.9%** | 0.05% | **6.2%** | 0.09% |
| all resource stalls (`resource_stalls.any`), share of cycles | 14.4% | 1.3% | 15.4% | 0.8% |
| **blocked store forwards** (`ld_blocks.store_forward`) per 1000 instructions | **10.6** | 0.27 | **11.2** | 0.06 |
| cycles with no µop executed (`uops_executed.core_cycles_none`) | 13.7% | 10.2% | 10.7% | 5.7% |

The top-down rows for Lean are SW-2426's. Native's are from this run's events, the same formulas, and agree with SW-2426's within 0.5 points.

What it says:
- **Not the front end.** Native's frontend-bound share is *lower* than Lean's on both. Native does have a large instruction footprint: 29–31 L1i misses per 1000 instructions, and only 22–25% of µops from the µop cache. But Lean loses more slots there, so the front end doesn't explain the gap.
- **Not memory.** The memory-stall shares are close (SW-2426).
- **Bad speculation adds little:** 1.6 and 3.2 points more than Lean, with about 1 branch miss per 1000 instructions.
- **The gap is backend core-bound:** 17.5% and 18.0% of slots against Lean's 2–3%. The resource-stall events place it:
  - the store buffer is full for 6% of cycles, against Lean's 0.05–0.09%;
  - and about 11 loads per 1000 instructions are blocked from forwarding from an earlier store, against Lean's 0.06–0.27.
  - A blocked forward costs on the order of 10+ cycles on Skylake, so these alone could account for much of the backend share. That's an inference; their stalls overlap.
- **Where:** sampling `ld_blocks.store_forward` on expressions puts 16% of the blocks in `stitchwort_rt::value::free`, 16% in `sw_apply_prepare`, 9% in mimalloc's allocation path, 7% in `Value::data::<2>`, 7% in `sw_closure` and 6% in `sw_eff_step`. Sampling `resource_stalls.sb` puts 11% in `sw_eff_step`, 10% in `sw_apply_prepare`, 6% in `Std.Parse.%elim/value` (generated) and 6% in `sw_closure`.
- **The likely cause:** the runtime copies and frees 24-byte values through memory: argument arrays in `sw_apply_prepare`, closure captures in `sw_closure`, fields in the drop walk.
  - A value written with one width (two 16-byte or three 8-byte stores) and read back with another can't be forwarded, and the many stores fill the buffer.
  - This is a guess from where the events fall, not traced instruction by instruction.
  - It ties SW-2432 to value width: a 16-byte value (E) moves as one 16-byte store and load, and one word (A) as one 8-byte store.
  - It also suggests a cheaper fix independent of E: in those few runtime functions, copy values with the same widths they are later read with.

## Reproducing

Scripts (not committed; in the Overmind session's scratchpad):
- `record.py` builds with `--pc-map`, runs `perf record` and the SW-2432 `perf stat` sets.
- `classify.py NAME` classifies one program's samples as above, writing `NAME.classes.json`.
- `summarise.py` prints the tables.
- `backend.py` counts the resource-stall events.

Run them inside `nix develop .#compare`, after `task bench:compare:check -- --runners native,lean`.
