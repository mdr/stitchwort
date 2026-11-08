# SW-2425: a census of the values a run makes (compact values, V0)

Lane SW-2425, Sonnet, 8 Nov 2026. It answers V0 of
[docs/proposals/compact-values.md](../proposals/compact-values.md) §5 (D3432): what a
run allocates, what it stores in the fields, and what that would be under the note's
options C, E and A. Everything here is **[measured]** by counters in the runtime, except the
C, E and A columns, which are **[derived]** by the formulas below from the measured counts.

## Go/no-go

**Go for E.** The test was: does E cut allocated bytes by at least 25% on at least half
of the decision set? It does on all six, by 30 to 37% (table below). E stays a stage.

- E: 30–37% on the decision set against the note's 30–40% **[estimate]**: inside it.
- A: 62–67% against 55–65%: a little above. Part of that is not "one-word values" but the
  closure layout I gave A (one allocation of 16 + 8k bytes, as Lean's), which cuts closures
  by about 70% by itself; closures are 35–50% of the bytes in the parser-shaped programs.
  Take A's figure as "A with Lean-style closures".
- C alone: 6–12% of allocated bytes (the header is 8 of 64 bytes in a two-field cell, and
  cells are only part of the bytes).
- Floats and numbers of 2^61 or more are absent: **no `Float` was stored anywhere**, and no
  `Nat` field reached 2^61 in any program. The only boxes A would need on the whole
  run are 3 `Int`s wider than 61 bits in pidigits (a_boxes = 3). The note's "essentially
  absent" is confirmed.

| Program | today (MB allocated) | C cut | E cut | A cut | peak C cut | peak E cut | peak A cut | boxes A needs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| binary-trees | 4,373.3 | 12% | 37% | 62% | 12% | 37% | 63% | 0 |
| matcher | 5,298.5 | 6% | 31% | 67% | 13% | 37% | 63% | 0 |
| dijkstra | 1,266.3 | 8% | 33% | 66% | 10% | 37% | 63% | 0 |
| octopus | 2,319.8 | 7% | 33% | 67% | 13% | 37% | 63% | 0 |
| memory-game | 3,360.3 | 7% | 36% | 64% | 11% | 33% | 66% | 0 |
| expressions | 43,010.1 | 6% | 30% | 67% | 13% | 37% | 63% | 0 |
| scan | 40,660.9 | 6% | 30% | 67% | 13% | 37% | 63% | 0 |
| disk | 12,673.4 | 9% | 34% | 65% | 14% | 38% | 62% | 0 |
| bridge | 14,082.0 | 6% | 31% | 67% | 13% | 37% | 62% | 0 |
| pidigits | 8,503.5 | 0% | 0% | 0% | 12% | 37% | 63% | 3 |

Cuts are the share of allocated bytes (peak columns: of peak live bytes) removed against
today. The first six rows are the decision set; scan, disk, bridge and pidigits are
extra. pidigits has no go/no-go: its bytes are `num-bigint` limbs (8.5 GB of 8.5 GB), as
the note said, and the representation does not touch them.

## What was measured, and how

**Instrument.** The cargo feature `value-census` on `stitchwort-rt`
(`crates/rt/src/value_census.rs` and `value_census/enabled.rs`). Off, every hook is an empty
`#[inline(always)]` function (the constructors `new_fun`, `new_delay`, `new_resume`,
`new_state_run` and `new_handler` are `Rc::new`), so shipped and test builds are unchanged;
the lane's only edits to hot files are those constructor calls and one-line hooks.
On, relaxed atomic counters are kept, and `STITCHWORT_VALUE_CENSUS=path` makes the
process write `key value` lines at exit (`atexit`). Built apart:
`cargo build --release -p stitchwort-cli --features stitchwort-rt/value-census --target-dir target/census`.

**What is counted.**

- Cells: at `alloc_trace::alloc`, the one place every machine cell allocation already passes
  through (by field count; the kind of every stored value); in-place refills (`CtorReuse`) are
  counted apart and not as allocations.
- `Fun` (by variant, with captures), `Delay`, `Resume`, `StateRun`, `Handler`: at the `Rc::new`.
- Arrays (at creation and when copied because shared, with their length; pushes in place
  counted but not sized), texts and big numbers (`Value::text`, `Value::array`, `Value::nat`,
  `Value::int`; a few widening conversions in `prims.rs` are not counted).
- Live bytes under each model: added at allocation, taken off when the last reference to a
  cell, `Fun` or `Delay` goes (their `Drop`s). A check at exit finds nothing freed that was
  not counted.

**Sizes in this build** (`size_of`): `Value` 24, `Fun` 56 (its largest variant is `Jumped`
of two `Value`s, not `Pap`), `Delay` 72, `Handler` 72, `Resume` 80, `StateRun` 80, an `Rc`
header 16 (strong and weak counts).

**Formulas** (`n` fields, `k` captures, `m` array elements, `v` the `Value` slots of an
enum's largest variant: `Fun` 2, `Delay` 3, `Handler` 2, `Resume` 3, `StateRun` 3; `S` is the
`size_of`). Bytes are as asked of the allocator, with no rounding to size classes:

| object | today | C | E | A |
|---|---|---|---|---|
| cell | 16 + 24n | 8 + 24n | 8 + 16n | 8 + 8n |
| `Fun`, `Delay`, `Handler`, `Resume`, `StateRun` | 16 + S | 16 + S | 16 + S - 8v | 8 + S - 16v |
| closure's or pap's captures (a second allocation) | 24k | 24k | 16k | none |
| closure under A (one allocation) | | | | 16 + 8k |
| pap under A | | | | 24 + 8k |
| `Jumped` under A | | | | 24 |
| other `Fun`s under A | | | | 16 |
| array | 40 + 24m | 40 + 24m | 40 + 16m | 24 + 8m |
| text of `len` bytes | 16 + len | same | same (thin object) | same |
| big number of `l` limbs | 40 + 8l | same | same | same |
| scalar box under A (counted in "boxes") | | | | 16 each |

C touches cells only, as in the note (§3.1); E also shrinks every `Value`; A is Lean's
layout, with one allocation per closure. Under A a field or capture holding a `Float`, a
`Nat` of 2^61 or more, or an `Int` outside +-2^60 is a 16-byte box, added to A's total.
(Registers and arguments that hold such values would box as well; the census cannot see
those, but with no `Float` and no big `Nat` or `Int` in a run, there is nothing to box.)

**Totals** are cells + closures (`Fun`s with their captures) + delays + other (resume,
state-run and handler objects, arrays, texts, big numbers). **Peak** is the most live bytes of
cells, `Fun`s and `Delay`s at any moment; it leaves out arrays, texts, big numbers and the
`Resume`, `StateRun` and `Handler` objects, which have no free hook. That matters for
memory-game, whose peak is its one array: 30,002,052 elements, 720 MB today, 480 MB under E, 240 MB
under A; the "peak" column for it (cells only) is not its footprint.

## How the programs were run

On the bytecode machine (`stitchwort run`), not on native executables: a census of
what a program builds is the same on both (the machine and native code agree allocation
by allocation, which `alloc_trace` and its tests check), the machine builds every cell in
one place, and native code writes fields from generated code where a counter can't see
them. I did not compare the machine's counts with a native run's `sw_cell_new` counts
(`task profile:native`), so the agreement is the repository's claim and not re-checked here.

Every program ran at the **full comparison size** (bench/compare/programs.toml), none
over a minute: binary-trees 16 s, matcher 27 s, dijkstra 10 s, octopus 9 s,
memory-game 16 s, expressions 50 s, scan 45 s, disk 26 s, bridge 24 s, pidigits 2 s. Each answer
was checked against `expected.txt` (all equal). The counts include loading the project
(the `null` program's: 4 cells, one delay, so negligible).

## Per program

Each table: bytes allocated by class, under each model, then the peak.

### binary-trees

Cells 68,332,335 (136,664,607 fields, 0 more refilled in place); closures 21; paps 4; other funs 23; delays 1; resumes 18; handlers 2; arrays 0 (0 elements); texts 66; big numbers 0.

Cells by field count: 1: 63 (0%), 2: 68,332,272 (100%).

Cell fields by kind (136,664,607 stored): erased 0.0%, tag 50.3%, nat_lt_2^61 0.0%, cell 49.7%, fun 0.0%, text 0.0%.

Closure captures and pap arguments (53): tag 32.1%, nat_lt_2^61 5.7%, cell 30.2%, fun 32.1%.

| model (MB) | cells | closures | delays | other | total | vs today | peak live (MB, cells+closures+delays) | vs today |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| today | 4,373.3 | 0.0 | 0.0 | 0.0 | 4,373.3 | 100% | 67.1 | 100% |
| C | 3,826.6 | 0.0 | 0.0 | 0.0 | 3,826.6 | 88% | 58.7 | 88% |
| E | 2,733.3 | 0.0 | 0.0 | 0.0 | 2,733.3 | 63% | 41.9 | 63% |
| A (+ boxes) | 1,640.0 | 0.0 | 0.0 | 0.0 | 1,640.0 | 38% | 25.2 | 37% |

### matcher

Cells 42,914,413 (57,122,180 fields, 6,652,140 more refilled in place); closures 18,542,824; paps 1,710,073; other funs 4,818,487; delays 1; resumes 2,542,202; handlers 8; arrays 0 (0 elements); texts 1,826; big numbers 0.

Cells by field count: 1: 29,576,244 (69%), 2: 12,763,976 (30%), 3: 279,110 (1%), 4: 294,761 (1%), 5: 322 (0%).

Cell fields by kind (57,122,180 stored): erased 24.1%, tag 13.0%, nat_lt_2^61 2.0%, cell 48.9%, fun 12.0%, text 0.0%.

Closure captures and pap arguments (51,354,237): tag 9.2%, nat_lt_2^61 27.8%, cell 22.5%, fun 40.4%, text 0.0%.

| model (MB) | cells | closures | delays | other | total | vs today | peak live (MB, cells+closures+delays) | vs today |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| today | 2,057.6 | 2,996.6 | 0.0 | 244.4 | 5,298.5 | 100% | 36.2 | 100% |
| C | 1,714.2 | 2,996.6 | 0.0 | 244.4 | 4,955.2 | 94% | 31.7 | 87% |
| E | 1,257.3 | 2,198.3 | 0.0 | 183.4 | 3,638.9 | 69% | 22.6 | 63% |
| A (+ boxes) | 800.3 | 821.1 | 0.0 | 102.0 | 1,723.4 | 33% | 13.6 | 37% |

### dijkstra

Cells 13,091,315 (23,860,377 fields, 13,515,096 more refilled in place); closures 3,053,643; paps 1,360,708; other funs 131,521; delays 1; resumes 50,602; handlers 202; arrays 209 (800,200 elements); texts 105; big numbers 0.

Cells by field count: 1: 5,184,867 (40%), 2: 6,768,738 (52%), 3: 10,106 (0%), 4: 530,304 (4%), 5: 597,300 (5%).

Cell fields by kind (23,860,377 stored): erased 3.7%, tag 11.3%, nat_lt_2^61 42.9%, cell 32.4%, fun 9.7%, text 0.0%, array 0.0%.

Closure captures and pap arguments (6,894,564): tag 0.4%, nat_lt_2^61 8.0%, cell 4.8%, fun 86.8%, array 0.0%.

| model (MB) | cells | closures | delays | other | total | vs today | peak live (MB, cells+closures+delays) | vs today |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| today | 782.1 | 460.1 | 0.0 | 24.1 | 1,266.3 | 100% | 100.9 | 100% |
| C | 677.4 | 460.1 | 0.0 | 24.1 | 1,161.6 | 92% | 90.4 | 90% |
| E | 486.5 | 343.1 | 0.0 | 16.5 | 846.1 | 67% | 63.8 | 63% |
| A (+ boxes) | 295.6 | 128.2 | 0.0 | 8.5 | 432.3 | 34% | 37.2 | 37% |

### octopus

Cells 20,698,492 (41,144,288 fields, 4,012,781 more refilled in place); closures 6,964,783; paps 2,542; other funs 5,512; delays 1; resumes 2,122; handlers 43; arrays 90,910 (1,818,180 elements); texts 28; big numbers 0.

Cells by field count: 1: 254,036 (1%), 2: 20,443,576 (99%), 3: 420 (0%), 4: 460 (0%).

Cell fields by kind (41,144,288 stored): erased 7.5%, tag 0.0%, nat_lt_2^61 84.4%, cell 7.9%, fun 0.0%, text 0.0%, array 0.2%.

Closure captures and pap arguments (18,821,363): tag 0.0%, nat_lt_2^61 27.3%, cell 35.8%, fun 36.9%, array 0.0%.

| model (MB) | cells | closures | delays | other | total | vs today | peak live (MB, cells+closures+delays) | vs today |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| today | 1,318.6 | 953.7 | 0.0 | 47.5 | 2,319.8 | 100% | 0.2 | 100% |
| C | 1,153.1 | 953.7 | 0.0 | 47.5 | 2,154.2 | 93% | 0.2 | 87% |
| E | 823.9 | 691.6 | 0.0 | 32.9 | 1,548.4 | 67% | 0.1 | 63% |
| A (+ boxes) | 494.7 | 262.1 | 0.0 | 16.8 | 773.7 | 33% | 0.1 | 37% |

### memory-game

Cells 30,002,668 (90,007,068 fields, 31 more refilled in place); closures 171; paps 53; other funs 133; delays 1; resumes 52; handlers 5; arrays 2 (30,002,052 elements); texts 24; big numbers 0.

Cells by field count: 1: 333 (0%), 2: 286 (0%), 3: 30,002,033 (100%), 4: 16 (0%).

Cell fields by kind (90,007,068 stored): erased 0.0%, tag 0.0%, nat_lt_2^61 66.7%, cell 0.0%, fun 0.0%, text 0.0%, array 33.3%.

Closure captures and pap arguments (316): tag 7.3%, nat_lt_2^61 8.9%, cell 17.1%, fun 64.9%, text 1.9%.

| model (MB) | cells | closures | delays | other | total | vs today | peak live (MB, cells+closures+delays) | vs today |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| today | 2,640.2 | 0.0 | 0.0 | 720.1 | 3,360.3 | 100% | 0.0 | 100% |
| C | 2,400.2 | 0.0 | 0.0 | 720.1 | 3,120.3 | 93% | 0.0 | 89% |
| E | 1,680.1 | 0.0 | 0.0 | 480.0 | 2,160.2 | 64% | 0.0 | 67% |
| A (+ boxes) | 960.1 | 0.0 | 0.0 | 240.0 | 1,200.1 | 36% | 0.0 | 34% |

### expressions

Cells 322,399,246 (542,760,658 fields, 25,929,900 more refilled in place); closures 106,429,698; paps 29,495,342; other funs 86,609,711; delays 1; resumes 49,179,422; handlers 267,843; arrays 0 (0 elements); texts 2,138,405; big numbers 0.

Cells by field count: 1: 122,251,834 (38%), 2: 187,195,692 (58%), 3: 5,689,440 (2%), 4: 7,262,280 (2%).

Cell fields by kind (542,760,658 stored): erased 2.6%, tag 10.9%, nat_lt_2^61 4.9%, cell 53.1%, fun 27.5%, text 0.9%.

Closure captures and pap arguments (196,570,989): tag 13.8%, nat_lt_2^61 4.1%, cell 16.0%, fun 65.7%, text 0.3%.

| model (MB) | cells | closures | delays | other | total | vs today | peak live (MB, cells+closures+delays) | vs today |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| today | 18,184.6 | 20,032.3 | 0.0 | 4,793.1 | 43,010.1 | 100% | 218.5 | 100% |
| C | 15,605.4 | 20,032.3 | 0.0 | 4,793.1 | 40,430.9 | 94% | 191.2 | 87% |
| E | 11,263.4 | 15,135.2 | 0.0 | 3,608.5 | 30,007.1 | 70% | 136.6 | 63% |
| A (+ boxes) | 6,921.3 | 5,282.3 | 0.0 | 2,028.4 | 14,232.0 | 33% | 81.9 | 37% |

### scan

Cells 293,786,354 (512,492,313 fields, 7,903,403 more refilled in place); closures 92,048,677; paps 30,635,225; other funs 92,354,072; delays 1; resumes 47,496,430; handlers 4; arrays 0 (0 elements); texts 436,805; big numbers 0.

Cells by field count: 1: 101,594,813 (35%), 2: 177,621,331 (60%), 3: 2,626,002 (1%), 4: 11,944,208 (4%).

Cell fields by kind (512,492,313 stored): erased 2.0%, tag 12.7%, nat_lt_2^61 3.8%, cell 53.9%, fun 25.7%, text 1.9%.

Closure captures and pap arguments (180,913,527): tag 10.0%, nat_lt_2^61 3.4%, cell 21.1%, fun 65.5%, text 0.1%.

| model (MB) | cells | closures | delays | other | total | vs today | peak live (MB, cells+closures+delays) | vs today |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| today | 17,000.4 | 19,089.4 | 0.0 | 4,571.1 | 40,660.9 | 100% | 257.8 | 100% |
| C | 14,650.1 | 19,089.4 | 0.0 | 4,571.1 | 38,310.6 | 94% | 225.6 | 87% |
| E | 10,550.2 | 14,446.6 | 0.0 | 3,431.2 | 28,427.9 | 70% | 161.1 | 63% |
| A (+ boxes) | 6,450.2 | 5,067.3 | 0.0 | 1,911.3 | 13,428.9 | 33% | 96.7 | 37% |

### disk

Cells 148,581,811 (274,167,405 fields, 25,951,491 more refilled in place); closures 18,450,020; paps 5,400,005; other funs 11,700,022; delays 1; resumes 4,500,005; handlers 4; arrays 0 (0 elements); texts 5; big numbers 0.

Cells by field count: 1: 59,014,472 (40%), 2: 76,661,252 (52%), 3: 900,001 (1%), 4: 900,004 (1%), 5: 11,106,082 (7%).

Cell fields by kind (274,167,405 stored): erased 6.6%, tag 18.1%, nat_lt_2^61 27.7%, cell 39.7%, fun 7.9%, text 0.0%.

Closure captures and pap arguments (35,550,007): tag 7.6%, nat_lt_2^61 11.4%, cell 15.2%, fun 65.8%.

| model (MB) | cells | closures | delays | other | total | vs today | peak live (MB, cells+closures+delays) | vs today |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| today | 8,957.3 | 3,283.2 | 0.0 | 432.9 | 12,673.4 | 100% | 709.1 | 100% |
| C | 7,768.7 | 3,283.2 | 0.0 | 432.9 | 11,484.8 | 91% | 612.4 | 86% |
| E | 5,575.3 | 2,473.2 | 0.0 | 324.9 | 8,373.4 | 66% | 440.5 | 62% |
| A (+ boxes) | 3,382.0 | 882.0 | 0.0 | 180.9 | 4,444.9 | 35% | 268.6 | 38% |

### bridge

Cells 105,882,613 (187,916,882 fields, 15,029,400 more refilled in place); closures 39,019,058; paps 8,830,202; other funs 22,764,911; delays 1; resumes 9,519,602; handlers 255,002; arrays 0 (0 elements); texts 510,005; big numbers 0.

Cells by field count: 1: 34,770,444 (33%), 2: 63,915,769 (60%), 3: 3,470,700 (3%), 4: 3,725,700 (4%).

Cell fields by kind (187,916,882 stored): erased 2.3%, tag 12.4%, nat_lt_2^61 15.5%, cell 48.1%, fun 21.7%, text 0.1%.

Closure captures and pap arguments (85,540,659): tag 6.8%, nat_lt_2^61 31.1%, cell 21.6%, fun 40.2%, text 0.1%.

| model (MB) | cells | closures | delays | other | total | vs today | peak live (MB, cells+closures+delays) | vs today |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| today | 6,204.1 | 6,925.3 | 0.0 | 952.6 | 14,082.0 | 100% | 240.5 | 100% |
| C | 5,357.1 | 6,925.3 | 0.0 | 952.6 | 13,235.0 | 94% | 210.4 | 87% |
| E | 3,853.7 | 5,181.8 | 0.0 | 720.1 | 9,755.6 | 69% | 150.3 | 63% |
| A (+ boxes) | 2,350.4 | 1,866.6 | 0.0 | 409.3 | 4,626.4 | 33% | 90.2 | 38% |

### pidigits

Cells 128,346 (261,766 fields, 11,011 more refilled in place); closures 3,013; paps 4; other funs 2,006; delays 1; resumes 2,001; handlers 2; arrays 0 (0 elements); texts 14,000; big numbers 294,751.

Cells by field count: 1: 28,135 (22%), 2: 67,002 (52%), 3: 33,209 (26%).

Cell fields by kind (261,766 stored): erased 19.1%, tag 4.2%, nat_lt_2^61 11.9%, int_in_61_bits 0.0%, int_wider_than_61_bits 0.0%, bigint 38.0%, cell 19.9%, fun 2.7%, text 4.2%.

Closure captures and pap arguments (5,017): tag 39.9%, nat_lt_2^61 19.9%, cell 20.1%, fun 20.1%.

| model (MB) | cells | closures | delays | other | total | vs today | peak live (MB, cells+closures+delays) | vs today |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| today | 8.3 | 0.5 | 0.0 | 8,494.7 | 8,503.5 | 100% | 1.3 | 100% |
| C | 7.3 | 0.5 | 0.0 | 8,494.7 | 8,502.5 | 100% | 1.1 | 88% |
| E | 5.2 | 0.4 | 0.0 | 8,494.6 | 8,500.2 | 100% | 0.8 | 63% |
| A (+ boxes) | 3.1 | 0.1 | 0.0 | 8,494.6 | 8,497.8 | 100% | 0.5 | 37% |


## Reading the numbers

- **E clears the bar everywhere.** Cells are 8 + 16n against 16 + 24n: 37.5% off a
  two-field cell, 33% off a one-field cell. The two-field cell is 100% of binary-trees,
  99% of octopus, 30–60% elsewhere (matcher is mostly one-field cells). Closures shrink by
  about 25% under E (the `Rc<Fun>` from 72 to 56 bytes, captures from 24 to 16 each), the other
  objects by 25%. The
  low end (30%, expressions and scan) is where closures and effect objects, which E
  shrinks less than cells, are most of the bytes.
- **Closures and effect objects are half the bytes in the parser programs.** In
  expressions and scan (the two big ones) cells are 42% of today's bytes, closures 47%,
  everything else 11% (4.8 GB of `Resume` objects: 49 million of them, 96 bytes each, plus
  state-passing handler objects). That is the note's "the count of allocations dominates"
  for the parsers: C+E leave 70% of those bytes, and only removing allocations (SW-2135,
  SW-2322, operations in place) or A's single-allocation closure goes further. A's 67% for
  them is mostly the closure layout.
- **Peak live is cut by the same factors as allocated bytes** (E 37%, A 63% almost
  everywhere), because cells dominate what is live. Peaks of tracked objects: binary-trees
  67 MB (SW-2363 measured 69 MB for the process, so the counter is right), disk 709 MB,
  expressions 219 MB, scan 258 MB, bridge 241 MB, dijkstra 101 MB, matcher 36 MB, octopus 0.2 MB.
- **Fields hold no floats and no big scalars.** Cell fields, all programs: `Float` 0,
  `Nat` from 2^61 up 0, `Int` outside 61 bits 3 (pidigits). Only pidigits has big numbers
  (294,751 `BigInt`s, 38% of its cell fields). No scalar box would be needed under A in any
  decision-set program.
- **What cells hold** (decision set, share of stored fields): a pointer to a cell 0–53%
  (binary-trees 50%, expressions 53%, octopus 8%); a constructor tag with no fields 0–50%
  (binary-trees' leaves are half its fields); `Nat` below 2^61 0–84% (octopus 84%,
  memory-game 67%, dijkstra 43%); closures 0–28% (expressions 28%, matcher 12%).

## Surprises

- **Erased values are stored in cells.** 24% of matcher's cell fields are `Erased` (also
  7.5% in octopus, 6.6% in disk, 3.7% in dijkstra, 19% in pidigits). Each is a 24-byte slot
  (16 under E, 8 under A) that holds nothing. Matcher: 14 million erased fields. A field
  that is always erased could be dropped from the cell (SW-2415, determined fields, is the
  nearest ticket); worth checking which constructors they come from (probably a
  proof-carrying field kept at run time, or a type argument).
- **Closures are 26–57% of the allocated bytes** (matcher 57%, bridge 49%, expressions
  and scan 47%, octopus 41%, dijkstra 36%, disk 26%), so a closure layout of one allocation
  is a bigger prize than the cell header: A's closure (16 + 8k) against today's two
  allocations (72 + 24k) is a cut of 3x or more by itself. E could take it separately: one allocation
  for `Fun::Closure` with its captures inline needs no change to `Value`.
- **Each `jump`-using handler step makes three small objects.** `StateK`, `JumpK` and
  `Jumped` are each 72 bytes and are made together: 18.6 million of each in expressions,
  22.4 million in scan. They're the same shape every
  time; `Fun::JumpK` carries nothing, so a shared constant (one `Rc<Fun>` cloned) would save
  18–22 million allocations in those two programs, 1.3 to 1.6 GB in all. (A finding, below.)
- **Arrays are copied.** dijkstra makes 209 arrays of 800,200 elements in total and
  octopus 90,910 of 1,818,180: they are small except in memory-game's two (30 M elements).
  Nothing odd there.
- **No reuse in binary-trees** (0 cells refilled in place, all 68 M allocated); matcher, disk
  and bridge refill 6–26 million cells.
- Floats and big numbers are not common anywhere: the surprise the note asked about is that
  there isn't one.

## What I did not do

- No native run: see above. Native-only paths (the cell cache inlining allocation) are
  not counted; `alloc_at` (native cells whose fields are written later) is not hooked.
- No timings: the counters slow the runs (atomics on every allocation), so the
  seconds above are not the programs' speeds.
- `Resume`, `StateRun`, `Handler`, arrays, texts and big numbers have no free hook, so
  the peak leaves them out. Their E and A sizes use the largest variant's `Value` slots,
  not each variant's.
- Allocator size classes (mimalloc rounds 40, 56, 72 up) are not modelled; the note
  flagged the same.
- A's closure and the scalar boxes are the model's, not a design. C's header is 8 bytes
  as in §3.1; its freed-cell work-list trick is not modelled.

## Findings worth filing

- **Share `JumpK`.** It has no fields; every state-passing handler step allocates one
  (18.6 M in expressions, 22.4 M in scan). A shared `Rc<Fun>` per run removes them.
  Sonnet, about 30 min. (`machine.rs:891`, `native_abi.rs:2938`.)
- **Erased fields in cells.** Find which constructors (matcher: 24% of its fields) store
  `Erased`, and whether lowering can drop those fields. Opus or Sonnet, 1 h to find, then
  it joins SW-2415.
- **Add `value-census` to `task profile:native`'s family**, or a `task census` that builds the
  census binary and runs the programs of programs.toml, if V4 reruns it at decision time.
  Sonnet, 30 min. The driver used here is a 20-line Python script over `compare.Program`;
  it is not committed.

## Reproducing

```
nix develop -c cargo build --release -p stitchwort-cli --features stitchwort-rt/value-census --target-dir target/census
STITCHWORT_VALUE_CENSUS=/path/out.txt target/census/release/stitchwort run <target> [-- args]   # in aoc/ for an AoC function
```

The output is `key value` lines (counts and bytes); `size_of.*`, `cells.arity.N`,
`cell_field.<kind>`, `capture.<kind>`, `fun.<variant>`, `bytes.<class>.<model>`,
`peak.<model>`, `a_boxes`. The raw files for this run are in the lane's scratchpad only.

Test: `cargo test --release -p stitchwort-rt --features value-census --lib value_census`
(one test, run alone because the counters are the process's).
