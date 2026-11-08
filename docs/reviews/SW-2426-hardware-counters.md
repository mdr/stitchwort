# SW-2426: hardware counters on Overmind (compact values, step V1)

Step V1 of [`docs/proposals/compact-values.md`](../proposals/compact-values.md) (§5): how much of native code's time is spent waiting for memory, against Lean's, on the ten `bench/compare` programs. Measured on 8 Nov 2026, 18:39 to 18:50 GMT, on `7260862da`.

## The reading

**Go/no-go: the condition is not met.** Native's memory-stall share is under 10% on four of the five decision programs other than binary-trees, but **memory-game is at 14.3%**:

| Decision program | native memory-stall share | under 10%? |
|---|---:|---|
| binary-trees (excepted) | 23.1% | (excepted) |
| memory-game | **14.3%** | **no** |
| dijkstra | 8.6% | yes |
| expressions | 8.5% | yes |
| octopus | 5.1% | yes |
| matcher | 4.8% | yes |

So the note's conclusion, that the footprint half of the bet is worth under about 5%, V4 rests on instructions alone and B is ruled out, doesn't follow as stated. Read narrowly, the footprint matters in two places:

- **binary-trees:** 23.1% of native cycles are memory stalls, against 8.2% for Lean, and 12.5% are stalls on an L3 miss, against 1.8%. Native has 22× Lean's LLC misses and about 1100× its dTLB misses. This is at the bottom of the note's 25–40% estimate.
- **memory-game:** 14.3% of native's cycles (2.0 G) are memory stalls. That's about as many cycles as Lean's whole run (1.95 G), and 2.4× Lean's own stall cycles (0.85 G). Native has 2.4× Lean's LLC misses and about 580× its dTLB misses, which fits the note's §1.3 reading of a 720 MB array against Lean's 240 MB: page faults and TLB misses, not per-access misses. Lean waits more as a share (43.4%), as the note expected, but only because it does 16× fewer instructions.
- **Elsewhere,** the AoC programs and the parsers are at 4.8–8.6%. That's inside the note's 5–15% estimate, close to Lean's share (2.9–11.3%), and their L3-miss stalls are 0.0–1.9%. There the gap is instructions and, on the parsers, IPC: native 1.99–2.11 against Lean's 2.66–2.94, with memory stalls only about 2 points above Lean's.

A suggested rewording of the go/no-go for V4 (my reading, the orchestrator's or Matt's call): the footprint is worth modelling for binary-trees and memory-game only. For the other four decision programs, V4 can rest on instruction counts.

## How it was measured

- **Machine:** Overmind, an Intel Core i7-6700HQ (Skylake, 4 cores, 2 threads each), 15.5 GB, Linux 6.18.60, perf 7.2.9. Load about 0.9 to 1.0 throughout, and nothing else running.
- **Programs:** the harness's own commands and scaled inputs. `collect.py` imports `bench/compare/compare.py`'s `Program` and runs `Program.command("native" | "lean")` with the same stdin.
- **Builds:** rebuilt by `nix develop .#compare -c task bench:compare:check -- --runners native,lean` on this commit, which passed 22 of 22 answer checks. Every one of the 80 counted runs also printed the expected answer.
- **Event sets:** two sets per program and runner, two runs each, with the means reported below.
  1. `perf stat -x , -e cycles,instructions,L1-dcache-load-misses,LLC-load-misses,dTLB-load-misses,cycle_activity.stalls_l2_miss,cycle_activity.stalls_l3_miss,cycle_activity.stalls_mem_any`, as in the note.
  2. The level-1 top-down events, in place of `-M TopdownL1`. See the deviations below.
- **Spread:** cycles and instructions agree within 2.8% between the two runs everywhere, and within 1% on most programs. Each program's spread is under its table.

### Deviations from the brief

1. **`-M TopdownL1` doesn't work at `perf_event_paranoid` 2.** The metric needs the any-thread event `INT_MISC.RECOVERY_CYCLES_ANY`, which perf reports as `<not supported>`, so it prints no bad-speculation or backend figure.
   - I counted the level-1 events myself: `cpu_clk_unhalted.thread`, `idq_uops_not_delivered.core`, `uops_issued.any`, `uops_retired.retire_slots`, and `int_misc.recovery_cycles`, the per-thread form.
   - I used the standard Skylake level-1 formulas, with slots = 4 × cycles:
     - retiring = retire_slots / slots
     - frontend = idq_uops_not_delivered / slots
     - bad speculation = (uops_issued − retire_slots + 4 × recovery_cycles) / slots
     - backend = 1 − the other three
   - That's the formula for a core whose sibling thread is idle, which was true here; Hyper-Threading is on.
   - Changing the sysctl is Matt's call, so I didn't.
2. **User space only.** At paranoid 2, perf counts `:u` events, so the kernel's page-fault handling isn't in the cycles. That probably *understates* memory-game's and binary-trees' footprint cost.
3. **Multiplexed.** Skylake has 4 general counters per thread with Hyper-Threading on, and the NMI watchdog takes one. So the 8-event set was sampled at about 49–62% of each run and scaled up by perf, and the top-down set at about 79%. The shares mix events from different sampling windows, so treat differences under about 2 points as noise.
4. **`stalls_mem_any` overlaps the other two.** It counts cycles stalled with an L1 miss outstanding; `stalls_l2_miss` and `stalls_l3_miss` are subsets of it. It's an upper bound on what a smaller footprint could remove, not a prediction.

## Summary

| Program | decision | native IPC | Lean IPC | native mem stall | Lean mem stall | native L3-miss stall | native backend | native retiring |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| pidigits |  | 2.12 | 2.10 | 8.1% | 10.2% | 0.0% | 22.8% | 67.8% |
| binary-trees | yes | 2.55 | 2.95 | 23.1% | 8.2% | 12.5% | 26.4% | 60.1% |
| memory-game | yes | 2.53 | 1.16 | 14.3% | 43.4% | 10.0% | 25.2% | 60.5% |
| dijkstra | yes | 2.20 | 2.09 | 8.6% | 7.6% | 1.6% | 13.0% | 55.2% |
| octopus | yes | 2.54 | 3.22 | 5.1% | 2.9% | 0.0% | 7.5% | 63.6% |
| disk |  | 2.37 | 2.49 | 7.6% | 11.3% | 1.9% | 16.4% | 60.0% |
| expressions | yes | 1.99 | 2.66 | 8.5% | 6.4% | 0.4% | 17.5% | 51.8% |
| scan |  | 2.11 | 2.94 | 6.7% | 4.7% | 0.1% | 18.0% | 55.0% |
| matcher | yes | 2.45 | 2.70 | 4.8% | 6.8% | 0.1% | 8.5% | 61.7% |
| bridge |  | 2.15 | 2.46 | 7.0% | 7.0% | 0.7% | 14.2% | 55.5% |

Stall shares are of cycles; the top-down shares are of issue slots. Lean's binaries are `lake build` executables from `bench/compare/lean`.

## Per program

Each table is the mean of two runs.
- instructions and cycles are perf's scaled counts.
- IPC = instructions / cycles.
- mem stall = `stalls_mem_any` / cycles.
- L2-miss stall and L3-miss stall = `stalls_l2_miss` and `stalls_l3_miss` / cycles.
- The miss rows are counts.
- retiring, bad speculation, frontend and backend are the level-1 top-down shares.
- The last column is native ÷ Lean.
### pidigits

| | native | Lean | native ÷ Lean |
|---|---:|---:|---:|
| instructions | 9.47 G | 13.29 G | 0.71 |
| cycles | 4.46 G | 6.33 G | 0.70 |
| IPC | 2.12 | 2.10 | 1.01 |
| mem stall | 8.1% | 10.2% | 0.79 |
| L2-miss stall | 2.1% | 1.5% | 1.36 |
| L3-miss stall | 0.0% | 0.0% | 0.38 |
| L1d misses | 548.18 M | 1.09 G | 0.50 |
| LLC misses | 8.66 k | 9.85 k | 0.88 |
| dTLB misses | 4.32 k | 5.42 k | 0.80 |
| retiring | 67.8% | 54.7% | 1.24 |
| bad speculation | 0.6% | 0.9% | 0.68 |
| frontend | 8.8% | 5.1% | 1.73 |
| backend | 22.8% | 39.4% | 0.58 |

Run-to-run spread of cycles or instructions: native 0.1%, Lean 2.3%. Least-sampled event: native 49%, Lean 49% of the run.

### binary-trees (decision set)

| | native | Lean | native ÷ Lean |
|---|---:|---:|---:|
| instructions | 21.61 G | 9.81 G | 2.20 |
| cycles | 8.48 G | 3.33 G | 2.55 |
| IPC | 2.55 | 2.95 | 0.86 |
| mem stall | 23.1% | 8.2% | 2.82 |
| L2-miss stall | 14.0% | 2.0% | 6.91 |
| L3-miss stall | 12.5% | 1.8% | 6.99 |
| L1d misses | 149.61 M | 27.87 M | 5.37 |
| LLC misses | 10.91 M | 497.14 k | 21.94 |
| dTLB misses | 1.54 M | 1.41 k | 1096.97 |
| retiring | 60.1% | 72.0% | 0.83 |
| bad speculation | 2.5% | 2.0% | 1.27 |
| frontend | 11.0% | 21.8% | 0.50 |
| backend | 26.4% | 4.2% | 6.31 |

Run-to-run spread of cycles or instructions: native 0.6%, Lean 1.4%. Least-sampled event: native 49%, Lean 49% of the run.

### memory-game (decision set)

| | native | Lean | native ÷ Lean |
|---|---:|---:|---:|
| instructions | 35.50 G | 2.27 G | 15.64 |
| cycles | 14.01 G | 1.95 G | 7.19 |
| IPC | 2.53 | 1.16 | 2.18 |
| mem stall | 14.3% | 43.4% | 0.33 |
| L2-miss stall | 10.2% | 40.6% | 0.25 |
| L3-miss stall | 10.0% | 38.4% | 0.26 |
| L1d misses | 60.27 M | 34.12 M | 1.77 |
| LLC misses | 12.07 M | 4.99 M | 2.42 |
| dTLB misses | 1.02 M | 1.77 k | 576.46 |
| retiring | 60.5% | 24.1% | 2.51 |
| bad speculation | 3.2% | 9.0% | 0.36 |
| frontend | 11.1% | 18.4% | 0.60 |
| backend | 25.2% | 48.5% | 0.52 |

Run-to-run spread of cycles or instructions: native 2.0%, Lean 2.1%. Least-sampled event: native 49%, Lean 49% of the run.

### dijkstra (decision set)

| | native | Lean | native ÷ Lean |
|---|---:|---:|---:|
| instructions | 19.61 G | 1.51 G | 13.01 |
| cycles | 8.93 G | 720.96 M | 12.39 |
| IPC | 2.20 | 2.09 | 1.05 |
| mem stall | 8.6% | 7.6% | 1.13 |
| L2-miss stall | 2.4% | 0.4% | 5.34 |
| L3-miss stall | 1.6% | 0.3% | 5.09 |
| L1d misses | 166.90 M | 4.64 M | 35.97 |
| LLC misses | 1.59 M | 10.06 k | 157.89 |
| dTLB misses | 255.16 k | 1.83 k | 139.70 |
| retiring | 55.2% | 54.0% | 1.02 |
| bad speculation | 3.1% | 8.8% | 0.35 |
| frontend | 28.7% | 32.7% | 0.88 |
| backend | 13.0% | 4.5% | 2.90 |

Run-to-run spread of cycles or instructions: native 1.6%, Lean 2.8%. Least-sampled event: native 49%, Lean 49% of the run.

### octopus (decision set)

| | native | Lean | native ÷ Lean |
|---|---:|---:|---:|
| instructions | 28.99 G | 2.49 G | 11.63 |
| cycles | 11.41 G | 775.32 M | 14.72 |
| IPC | 2.54 | 3.22 | 0.79 |
| mem stall | 5.1% | 2.9% | 1.74 |
| L2-miss stall | 0.2% | 0.2% | 0.97 |
| L3-miss stall | 0.0% | 0.2% | 0.16 |
| L1d misses | 60.68 M | 313.34 k | 193.66 |
| LLC misses | 31.72 k | 2.77 k | 11.45 |
| dTLB misses | 44.27 k | 1.73 k | 25.64 |
| retiring | 63.6% | 72.3% | 0.88 |
| bad speculation | 3.2% | 3.4% | 0.94 |
| frontend | 25.6% | 20.9% | 1.23 |
| backend | 7.5% | 3.5% | 2.18 |

Run-to-run spread of cycles or instructions: native 0.5%, Lean 0.3%. Least-sampled event: native 49%, Lean 49% of the run.

### disk

| | native | Lean | native ÷ Lean |
|---|---:|---:|---:|
| instructions | 112.40 G | 6.33 G | 17.76 |
| cycles | 47.47 G | 2.54 G | 18.70 |
| IPC | 2.37 | 2.49 | 0.95 |
| mem stall | 7.6% | 11.3% | 0.67 |
| L2-miss stall | 2.2% | 2.7% | 0.84 |
| L3-miss stall | 1.9% | 1.9% | 0.97 |
| L1d misses | 685.39 M | 47.93 M | 14.30 |
| LLC misses | 7.85 M | 1.06 M | 7.37 |
| dTLB misses | 3.47 M | 11.32 k | 306.28 |
| retiring | 60.0% | 57.1% | 1.05 |
| bad speculation | 3.9% | 7.6% | 0.51 |
| frontend | 19.7% | 27.6% | 0.71 |
| backend | 16.4% | 7.6% | 2.16 |

Run-to-run spread of cycles or instructions: native 0.7%, Lean 0.9%. Least-sampled event: native 50%, Lean 49% of the run.

### expressions (decision set)

| | native | Lean | native ÷ Lean |
|---|---:|---:|---:|
| instructions | 344.52 G | 6.09 G | 56.60 |
| cycles | 172.76 G | 2.29 G | 75.49 |
| IPC | 1.99 | 2.66 | 0.75 |
| mem stall | 8.5% | 6.4% | 1.34 |
| L2-miss stall | 1.3% | 0.3% | 5.00 |
| L3-miss stall | 0.4% | 0.3% | 1.65 |
| L1d misses | 1.78 G | 2.01 M | 886.04 |
| LLC misses | 6.79 M | 30.21 k | 224.63 |
| dTLB misses | 7.35 M | 9.21 k | 798.38 |
| retiring | 51.8% | 63.5% | 0.82 |
| bad speculation | 6.5% | 4.9% | 1.33 |
| frontend | 24.2% | 28.7% | 0.84 |
| backend | 17.5% | 2.9% | 6.12 |

Run-to-run spread of cycles or instructions: native 0.1%, Lean 1.1%. Least-sampled event: native 50%, Lean 49% of the run.

### scan

| | native | Lean | native ÷ Lean |
|---|---:|---:|---:|
| instructions | 331.05 G | 6.00 G | 55.18 |
| cycles | 156.70 G | 2.04 G | 76.67 |
| IPC | 2.11 | 2.94 | 0.72 |
| mem stall | 6.7% | 4.7% | 1.42 |
| L2-miss stall | 0.5% | 0.4% | 1.27 |
| L3-miss stall | 0.1% | 0.4% | 0.24 |
| L1d misses | 969.65 M | 1.40 M | 693.38 |
| LLC misses | 1.46 M | 55.65 k | 26.24 |
| dTLB misses | 3.86 M | 1.83 k | 2103.49 |
| retiring | 55.0% | 70.5% | 0.78 |
| bad speculation | 5.3% | 2.1% | 2.55 |
| frontend | 21.7% | 25.3% | 0.86 |
| backend | 18.0% | 2.1% | 8.56 |

Run-to-run spread of cycles or instructions: native 0.7%, Lean 0.9%. Least-sampled event: native 49%, Lean 49% of the run.

### matcher (decision set)

| | native | Lean | native ÷ Lean |
|---|---:|---:|---:|
| instructions | 74.46 G | 8.09 G | 9.21 |
| cycles | 30.43 G | 3.00 G | 10.15 |
| IPC | 2.45 | 2.70 | 0.91 |
| mem stall | 4.8% | 6.8% | 0.70 |
| L2-miss stall | 0.3% | 0.2% | 1.59 |
| L3-miss stall | 0.1% | 0.1% | 1.66 |
| L1d misses | 315.90 M | 10.12 M | 31.21 |
| LLC misses | 314.56 k | 21.28 k | 14.78 |
| dTLB misses | 980.70 k | 2.62 k | 373.89 |
| retiring | 61.7% | 66.6% | 0.93 |
| bad speculation | 3.9% | 7.7% | 0.51 |
| frontend | 26.0% | 24.0% | 1.08 |
| backend | 8.5% | 1.7% | 4.90 |

Run-to-run spread of cycles or instructions: native 0.5%, Lean 1.4%. Least-sampled event: native 49%, Lean 49% of the run.

### bridge

| | native | Lean | native ÷ Lean |
|---|---:|---:|---:|
| instructions | 119.49 G | 7.03 G | 16.99 |
| cycles | 55.61 G | 2.86 G | 19.41 |
| IPC | 2.15 | 2.46 | 0.88 |
| mem stall | 7.0% | 7.0% | 1.00 |
| L2-miss stall | 1.0% | 0.7% | 1.40 |
| L3-miss stall | 0.7% | 0.7% | 1.05 |
| L1d misses | 331.15 M | 3.88 M | 85.39 |
| LLC misses | 2.84 M | 150.17 k | 18.89 |
| dTLB misses | 1.48 M | 5.59 k | 264.06 |
| retiring | 55.5% | 65.1% | 0.85 |
| bad speculation | 5.0% | 6.0% | 0.83 |
| frontend | 25.3% | 26.5% | 0.95 |
| backend | 14.2% | 2.4% | 5.95 |

Run-to-run spread of cycles or instructions: native 0.5%, Lean 2.3%. Least-sampled event: native 49%, Lean 49% of the run.


## Other observations

- **dTLB misses** are 3 to 4 orders of magnitude above Lean's on binary-trees (1.54 M against 1.41 k) and memory-game (1.02 M against 1.77 k). That's far more than the 2.7–3× footprint ratio alone explains. This machine has transparent huge pages on `madvise`, so one possible cause is that Lean's allocator asks for huge pages and mimalloc, as native uses it, doesn't. I haven't checked; it's worth a look in V3 or V4, since it would be a cheap win separate from value size.
- **Retiring** is 52–68% of native's slots on every program: it's mostly doing work, not waiting. That agrees with the note's §1.4 finding that the gap is mostly instruction count. Backend-bound is above 20% only on pidigits (`num-bigint`), binary-trees and memory-game.
- **Parsers:** expressions and scan have native's lowest IPC (1.99 and 2.11) against Lean's 2.66 and 2.94, with similar memory-stall shares. The rate gap there is not memory; frontend and bad speculation are worth a look in V2.

## Reproducing

The two scripts and the 80 raw CSV files were in the Overmind session's scratchpad. They weren't committed, so they're described here:

- `collect.py` runs, for each program, runner and set, `perf stat -x , -e <set> -- sh -c <Program.command(runner)>` twice, with the program's input on stdin.
- `analyse.py` averages the two runs and prints the tables above.

Run both inside `nix develop .#compare` after `task bench:compare:check -- --runners native,lean`. Collection takes about 11 minutes.
