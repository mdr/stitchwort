# SW-2441: register dilation (compact values, k measured)

Overmind (i7-6700HQ, Skylake), 8 Nov 2026, main at 7fff87a4e. Lane branch
`lane/SW-2441` holds the patch. Experiment for compact-values.md §7.5: native code carries a
fourth, unused word in every value it holds in registers and passes in calls; what that
costs is about what E's removal of the third word saves.

## Result

**The problem.** V4 (§7) predicted E (two-word values) at 1.088× on the decision set and
1.21× on binary-trees, just under the gate (1.10×, 1.25×), with the answer resting on k, the
time a removed instruction is worth, times V2's rule for how many spills and saves a word
causes.

**What I measured.** A fourth word costs binary-trees **+5.1% of cycles** and the decision
set **+4.5%** (mean and geometric mean) **[measured]**, against the "about 11% and 6–7%"
the note says E needs. It adds far fewer instructions than V2's rule assumed for a word
(binary-trees +4.0% against the rule's 14%), and each costs about its share of time: **k ≈ 1**
(pooled 1.24 on the decision set, 0.8–1.3 per program apart from memory-game).

**What it means.** Read as a mirror (removing the third word saves what adding a fourth
costs, plus V4's footprint and store-forwarding terms), E gives **1.16× on binary-trees and
1.09× on the decision set** at the central runtime share **[derived from measured inputs]**:
**E misses both gates**, binary-trees clearly. It clears them only with every other input at
its high value. Putting the measured k into V4's formula unchanged would say E passes
(1.36× and 1.16×), but that uses V2's instruction counts, which this experiment shows to be
about three times too high for binary-trees; I don't think that reading stands.

## The change

`n1.rs`, built with `SW_REGISTER_DILATION` set (`const W = 4`; unset, the code is as on
main, `W = 3`):

- `Val` is `[IrValue; W]`; registers are `W` Cranelift variables; the global, value and
  apply-stub signatures take and return `W` words a value, so the fourth word is passed in
  calls, returned, kept in block parameters across loops and spilled by the register
  allocator like any other.
- **Where w3 comes from.** A value read from memory gets one more load as its fourth word
  (`uload32` of its third word's address, a different opcode so Cranelift can't merge it
  with the load of the third). A value built in registers gives it its third word's SSA
  value: for the common constant third word (0) that is what a real constant fourth word
  would be after Cranelift's sharing of constants; it still needs its own argument
  register at a call, and its own block parameter.
- **Never stored:** cells, stack slots, the apply plan and the runtime's structs stay three
  words; stores to memory drop w3. The runtime's helpers (`sw_drop_words`, `sw_inc`, …) are
  still passed three words.
- No runtime ABI change: the trampolines are emitted by Cranelift and the runtime calls them
  with pointers. The effect runtime's bodies (`rt_loop`, `rt_resume`) keep three words a
  value as parameters and internally but return `W`, so the tail calls between them and
  the bodies still match.

Tests: `task test:lane AREA=native`, 70 of 70 pass on both builds; all 11 compare programs
give the right answers on both (`compare.sh --check`, and every timed run). Clippy clean on
both builds.

## Measurements

perf stat (user-space cycles and instructions) and wall time; two rounds, base and wide
interleaved; means. Cycles differed by at most about 2% between rounds (wall more: round 1
ran slower throughout). `*` the decision set.

| Program | instructions base | wide | Δ instructions | cycles base | wide | Δ cycles | time base | wide | Δ time | k |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| pidigits | 9.44 G | 9.45 G | +0.0% | 4.44 G | 4.45 G | +0.1% | 1.35 s | 1.33 s | −1.6% | – |
| binary-trees * | 21.28 G | 22.14 G | +4.0% | 8.17 G | 8.58 G | **+5.1%** | 2.88 s | 3.01 s | +4.5% | 1.27 |
| memory-game * | 35.79 G | 36.56 G | +2.1% | 14.12 G | 15.05 G | +6.6% | 4.87 s | 5.13 s | +5.3% | 3.06 |
| dijkstra * | 18.87 G | 19.83 G | +5.1% | 8.64 G | 9.06 G | +4.8% | 2.74 s | 2.85 s | +4.1% | 0.95 |
| octopus * | 27.45 G | 28.40 G | +3.4% | 10.74 G | 11.17 G | +4.0% | 3.20 s | 3.35 s | +4.9% | 1.17 |
| disk | 105.12 G | 108.23 G | +3.0% | 45.39 G | 46.87 G | +3.3% | 13.89 s | 14.31 s | +3.0% | 1.11 |
| expressions * | 327.21 G | 332.82 G | +1.7% | 163.24 G | 165.45 G | +1.4% | 47.61 s | 48.21 s | +1.3% | 0.79 |
| scan | 314.04 G | 320.25 G | +2.0% | 151.34 G | 154.29 G | +2.0% | 43.89 s | 44.70 s | +1.8% | 0.99 |
| matcher * | 72.63 G | 76.37 G | +5.2% | 29.81 G | 31.26 G | +4.9% | 8.65 s | 9.06 s | +4.8% | 0.94 |
| bridge | 113.36 G | 116.38 G | +2.7% | 52.83 G | 54.06 G | +2.3% | 15.45 s | 15.81 s | +2.3% | 0.88 |

Decision set: instructions +3.6%, cycles +4.5% (geometric mean +4.5%), time +4.1%;
**pooled k = 1.24** (cycles added ÷ instructions added, both as shares). memory-game's 3.06
is real in cycles (both rounds agree) but small in instructions: its fourth word costs
something other than instructions there, probably its wider calls around the big array's
accesses; I didn't look further.

**Where the added instructions are** (perf record, sampled instructions by kind, as a share
of base's instructions):

| kind | binary-trees | matcher |
|---|---:|---:|
| memory loads (mostly the synthesised w3 loads) | +1.82 | −0.93 |
| stack loads | +0.90 | +1.13 |
| stack stores | +0.54 | +3.62 |
| register moves | +0.73 | −0.51 |
| memory stores | +0.36 | −0.05 |
| other ALU, branches | +0.10 | +1.92 |
| push/pop (callee-saved) | −0.42 | −0.02 |

On binary-trees, spills, reloads and moves together add about 2.2 points, against V2's
rule's ≈ 8 points for a third of the stack traffic and saves (15.2% + 8.9%, a third) plus
half the moves. Cranelift's register allocator absorbs most of the extra word there; on
matcher the word lands mostly as stack stores, as the rule expected.

## V4's E prediction again

Same formula, S = k × I + F + W (§7.1), central F and W:

| Reading | binary-trees (gate 1.25) | decision-set geomean (gate 1.10) |
|---|---:|---:|
| V4 as written, k = 0.6, V2's I | 1.211 | 1.088 |
| measured pooled k = 1.24, V2's I | 1.359 | 1.164 |
| each program's measured k, V2's I | 1.365 | 1.188 |
| **mirror: the cycles a fourth word costs, + F + W, runtime share r = 0.3** | **1.165** | **1.090** |
| mirror, r = 0 / 0.6 | 1.164 / 1.165 | 1.076 / 1.106 |
| mirror, r = 0.6 and F, W at their high values | 1.253 | 1.142 |

The first three rows combine a k measured on this experiment's instructions with V2's
instruction counts, which this experiment contradicts (for a word, binary-trees +4.0% here
against V2's I of 14.0%; matcher 5.2% against 9.1%; expressions 1.7% against 4.4%). The
mirror uses one consistent measurement, and is if anything generous: register pressure is
convex, so removing the third word should save a little less than adding a fourth costs.

**Runtime side left out.** Only generated code is widened. V2's runtime bound for E (a
third of the drop walk's, the apply stubs' and `Value::clone`'s memory and stack accesses)
is 0.1% of instructions on binary-trees and 3.7–8.4% on the others; the mirror rows add it
back at r × the bound with k = 1. It moves the mean between 1.076 and 1.106, and
binary-trees not at all. Memory isn't widened either: cells' and stack slots' word-2
traffic is V2's "word 2" class and V4's F, which the mirror keeps at V4's values.

**Biases I know of.**
- The synthesised loads (about 1.8 points of binary-trees' 4.0%) are cheap, independent L1
  hits, which pulls k down there; a real word 2's loads are partly on dependent chains.
  Either way, they are cycles counted in the mirror.
- A fourth word that shares the third's SSA value has no live range of its own inside a
  block. Where the third word isn't a constant (a text's length, a cell's count), a real
  word would; this understates pressure a little.

## Recommendation

E doesn't clear the gate on this measurement: **hold E** (as V4 recommended), and do the
cheaper changes of §7.5 first. If anyone wants a second opinion before dropping E, the
next measurement is E itself on binary-trees only (a two-word `Val` for its types), not
another model.

## Reproducing

Scratchpad scripts (Overmind): `sw2441/build.sh base|wide` (builds the CLI and runtime, then
the programs through `compare.sh --check`), `collect.py DIR` (the two rounds),
`analyse.py DIR/raw` (the tables and the predictions), and `kinds.py DIR NAME` (instructions
by kind).
