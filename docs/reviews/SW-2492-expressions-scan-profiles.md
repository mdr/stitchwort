# Expressions and scan, profiled natively (SW-2492)

SW-2492, 9 Nov 2026, Sonnet, `lane/SW-2492` from `main` at `49ee8ba41` (after effect-runtime R1-R3
and SW-2487). Measurement and write-up only: no compiler, runtime or std code changed. The two
programs are the `expressions` (AoC 2020 day 18, the real input repeated 180 times: 66,959 lines,
3.41 MB) and `scan` (AoC 2024 day 3, repeated 200 times: 3.59 MB, 1,399 lines) entries of
`bench/compare/programs.toml`.

The latest comparison (SW-2295-comparative-speed.md, job 34) has native at 68x Lean on expressions
and 72x on scan by time. This note says where the time goes, in the programs' terms, what Lean's
versions do differently, and what to change, ranked.

**How to read the numbers.** The machine was loaded while this ran (load average 7 to 39, other
lanes building), so wall times are only for comparing runs made together. The unit used for
comparing is **instructions retired** (`/usr/bin/time -l`, as the comparison uses); shares inside
one profile are samply time. Everything is **measured** unless marked *estimated*, and an
estimate says how it was made. One run of each (instruction counts repeat to 0.05% or better,
SW-2463 §4.3). The natives were built non-incrementally by `task profile:native` in
`target/bench` (no kache), so they are comparable with job 34's, not with the lane-built numbers in
SW-2463 (SW-2474's 3%).

## 0. Summary

1. **Both programs are parsing and nothing else.** Expressions: reading and splitting 1.0%, parsing
   part 1 41.5%, part 2 56.7%, evaluating both 0.8%. Scan: reading 0.8%, parsing 99.2%, both parts'
   sums under 0.1%. Part 2's grammar has one more precedence level and costs 1.36 times part 1's.
2. **The cost is the number of `Parse` operations, about 12,000 to 16,000 instructions each.**
   Expressions performs 16.1 M operations (120 per line, 2.4 per character), scan 22.4 M (6.2 per
   character), at 16.6 K and 12.5 K instructions an operation, all in. Each operation builds
   about 24 objects (expressions) or 17 (scan), takes 5 to 8 effect steps, and pays 1.0 to 1.4 us (loaded machine).
   The effect runtime's own objects (R1 to R3's target) are a third of them (8.9 and 6.4 an
   operation); closures, generated code's cells and partial applications are the rest.
3. **The biggest wins are not in the runtime: they are fewer operations.** Measured with scratch
   variants that give the same answers:
   - scan with `Parse.findAllStarting` (an existing std function) instead of `findAll`: **279.3 G to
     31.0 G instructions, -88.9%**. 53% of the input is noise, and `findAll` pays about 10
     operations to reject each noise character; `findAllStarting` skips it with one `span`.
   - expressions with the operand chosen by looking at one character instead of `oneOf [nat, '(' ...]`:
     **-17.8%**; with also the operator chain written as a plain loop of `literal` tests (no
     `optional`, `mark`, `note`, `stop` per round): **268.4 G to 99.2 G, -63.0%**.
   - both: the character lists that `Parse.text` and `Parse.pick` build on every try
     (`"mul(".toList`) made once: **-5.8% scan, -3.9% expressions**; `pick`'s failure notes alone
     cost **13.6% of scan** (38 G over 3.8 M `note` operations, 10 K instructions each).
4. **R4 (SW-2464) re-estimated from today's counts: 2.9 to 5.0% on expressions, 4.0 to 6.9% on
   scan** (central 3.8% and 5%), above the proposal's 2.3 to 3.2% and 2.8 to 3.9%, because the
   measured cost of a removed cell (183 to 229 instructions, SW-2463) is above the 140 the
   proposal used, and R4 removes 33.6 M cells (17.5 M `Bind` nodes and 16.1 M `Done` cells) on
   expressions and 48.7 M on scan. **R5 (SW-2465): 1.2 to 1.8% and 1.6 to 2.4%.** Together about
   5% and 7%: worth doing, but a tenth of what the program-level changes give, and neither
   closes the Lean gap (instructions: 44x on expressions, 47x on scan).
5. **Lean's versions are hand-written byte scanners** (position argument, `hasAt` byte compares, no
   backtracking handlers, no per-character allocation but `hasAt`'s `toUTF8`). They do the same
   work in 6.09 G and 5.99 G instructions: about 890 and 1,670 instructions a character parsed
   (expressions parses each character twice). Ours is 39 K and 78 K. The remaining gap after the
   program-level changes is the operation cost of point 2.

Ranked targets (details in section 4):

| # | Target | Expressions | Scan | Basis |
|---|---|---:|---:|---|
| 1 | `findAllStarting` in day 3 (noise skipped by one `span`) | n/a | **-88.9%** | measured |
| 2 | One-character dispatch for the operand, then the operator chain as a loop of `literal` tests | **-63.0%** (-17.8% for the dispatch alone) | n/a | measured (upper bound: drops the back-up after an operator) |
| 3 | `pick`'s failure notes: one operation, or none until a failure is reported | -3% to -6% | -7% to -13.6% | scan measured when removed (13.6%); the halves estimated at the same cost per operation |
| 4 | Character lists for `text`/`pick`/`literal` made once, not per try | -3.9% | -5.8% | measured |
| 5 | R4 (SW-2464): `bind (Call o DoneK) k` is `Call o k` | -2.9% to -5.0% | -4.0% to -6.9% | estimated from tonight's per-object costs and today's counts |
| 6 | R5 (SW-2465): no resumption for a state handler without `k` | -1.2% to -1.8% | -1.6% to -2.4% | estimated, same method |
| 7 | R7: rebuilt forwarded operations (17.5 M cells expressions, 5.3 M scan) | -1.2% to -1.5% | -0.4% | estimated, 183 to 229 per cell |
| 8 | Closures: 6.5 an operation on expressions, 4.1 on scan (SW-2352, operations in place stage E) | not estimable | not estimable | counted only |
| 9 | Compact values, per-object cost (section 3.4) | not estimable | not estimable | |

## 1. Expressions (2020 day 18)

### 1.1 Stages

Natively built variants of the same program (scratch entry points in the AoC project, not
committed; section 6), each reading the same 3.4 MB input:

| Variant | Instructions (G) | Wall (s, loaded) | What it adds |
|---|---:|---:|---|
| read and split into lines (`input.lines.length`) | 2.70 | 0.33 | 1.0% of `main` |
| and `toList` of every line | 4.94 | 0.47 | the lists the parser reads: 2.2 G |
| part 1 parse (`parseHomework input samePrecedence`) | 113.89 | 8.9 | **111.2 G net: 41.5%** |
| part 2 parse | 154.43 | 11.9 | **151.7 G net: 56.7%** |
| part 1 parse and `sum` | 113.82 | 8.6 | evaluation: under 0.1 G |
| both (`main`) | 267.75 | 22.5 | evaluation of both parts 2.1 G (0.8%) |

Per line parse (134 K of them): 2.0 M instructions, 120 `Parse` operations, 14.5 operands, 19 rounds
of `chainLeft`'s `many`. The line is 51 characters.

### 1.2 Top functions (whole run, 45,315 samples)

By kind: runtime (Rust) 27.9%, allocator 26.5%, generated code 23.8%, `sw_*` entry points 20.4%.

| Function | self | note |
|---|---:|---|
| `mi_free` / `mi_malloc` | 8.1% / 7.2% | allocator, 15.3% (26.5% with `__rust_alloc` and the rest) |
| `sw_apply_prepare` | 7.9% | the slow apply: 127.7 M calls |
| `drop_glue::<Value>`, `value::free`, `Fun::take_children`, `Rc<Fun>::drop_slow`, `Fields::drop`, `Rc<[Value]>::drop_slow` | 7.6, 5.0, 3.3, 3.1, 3.0, 1.5% | freeing, 23.5% together |
| `sw_eff_step` | 7.0% | 131.0 M steps |
| `rt_loop`, `rt_resume`, `sw_resume_begin`, `effect::forwarded`, `state_step` | 3.3, 1.2, 1.1, 1.0, 1.0% | |
| `apply2`, `apply4`, `apply1` | 2.7, 1.8, 1.1% | calls through function values |
| `Std.Parse.%elim#102` | 2.1% | the fused `runFrom` state handler |
| `Value::clone`, `sw_closure` | 2.1%, 1.3% | |

Generated code is 23.8% of the run, and `Std.Parse*` is 8.2% of that, `Std.List*` 2.7%, the day's
own code 1.0%. No single compiled body is above 2.1%: this is a profile of the runtime, not of any
function. Inclusive times are not useful here (the profiler marks the handlers' frames), which is
why section 1.1's stage cuts are the split.

Instruction split of the hottest bodies (`--by-instruction`, top 12 bodies; from
`target/profile/expressions.json.gz`): `Std.Parse.%elim#102` is 44% the instructions' own work
(`Unpack`s of the state's fields), 20% prologue, 17% reference-count decrements, 16% untagged, 3%
calls. `Std.Text.stripPrefixChars` (8.3 M entries; `literal`'s test) is 41% untagged, 33% work,
12% decrements, 8% increments. `manyFuel/lambda70` (the round of `chainLeft`'s `many`) is 49% work,
30% prologue, 10% increments: it is mostly building closures (`Pap`, `Closure`: 23% of its
instructions). The shape is call overhead and reference counts, not the work of parsing.

### 1.3 Runtime calls (`call-counts` build)

| | expressions |
|---|---:|
| `Parse` operations first performed | 16.10 M (routed to a clause: 17.51 M) |
| `sw_eff_step` | 131.0 M |
| `sw_apply_prepare` | 127.7 M (partial application 52.7 M, eager resumption 26.4 M, closure 16.2 M, `DoneK` 16.1 M, `JumpK` 16.1 M) |
| `sw_closure` | 103.9 M |
| `sw_cell_new` (generated code) plus cache hits | 83.1 M + 45.1 M |
| `sw_bind`, `Bind` nodes pushed, popped | 44.1 M, 43.8 M, 39.9 M |
| forwarding clauses skipped | 26.4 M (1.64 an operation) |
| runtime objects (all sites) | 142.7 M (8.9 an operation) |
| `TextToList` | 3.28 M |

Operations by kind, routed to the state handler: `mark` 7.30 M (42%), `literal` 3.15 M (18%),
`span` or `next` 2.61 M (15%), `note` 1.64 M (9%), `reset` 1.41 M, `stop` 1.41 M (8% each).
Objects per operation: runtime 8.9, closures 6.5, generated code's cells 8.0, partial applications
0.7, about 24 in all.

### 1.4 The hot loop in the program's terms

`parseHomework` runs `Parse.eachLine` over the input: per line `Parse.recursive (self => level self
levels)`. `level` nests one `chain` per precedence level (one in part 1, two in part 2) around
`operand`. A line of 14.5 numbers and brackets costs, in operations:

- Each `chain` is `Parse.chainLeft term operator`, which reads `term`, then runs `Parse.many` of
  `operator(); operand()`. **One round of `many` costs a `mark`, an `optional` (a handler, and every
  operation inside it is forwarded through it: 26.4 M forwards), the operator, the operand, and a
  progress check.** The last round of each chain fails: 0.79 M times (inferred from `noteWords`' 2.38 M entries, three a failure) `pick` tries both operators with
  `literal`, notes the two words (`note`, `note`), stops (`stop`), and the handler resets (`reset`).
  That failure alone is 6 operations. The brackets add a failing `nat` (a `span` that returns `[]`,
  a `note`, a `stop`, a `reset`) for every operand that is a bracket, because `operand` is `oneOf [nat, '(' ...]`.
- Each operand is `oneOf`: `optional` (a `mark`, a handler) around `nat` (a `span` and `Nat.fromDigits`).
- `pick` makes a `List Char` of each operator's word on every try (3.28 M `TextToList`, one list of
  3 cells each), and `operator` maps its list of operators to a list of `(word, operator)` pairs on
  every call.

None of this is the arithmetic. The experiment of section 1.5 removes the `oneOf`, `many` and `pick`
and keeps everything else.

### 1.5 Scratch grammars (same answers, 268.4 G is the unchanged grammar in the scratch project)

| Variant | Instructions (G) | Change | Operations | Eff steps |
|---|---:|---:|---:|---:|
| the day's grammar (`exBase`) | 268.38 | | 16.10 M | 131.0 M |
| handler ignores `note` (`exQuiet`) | 265.78 | -0.97% | | |
| operator character lists made once (`exConst`) | 257.97 | **-3.88%** | 16.10 M | 131.0 M |
| operand by one character: `Parse.next (c => c == '(')` (`exOperand`) | 220.59 | **-17.80%** | 15.84 M | 115.3 M |
| and the chain as a loop, `literal` per operator, no `optional`/`mark`/`note`/`stop` (`exFused`) | 99.16 | **-63.05%** | 8.37 M | 46.7 M |

All five print `2751445354966740 83033146361942280`, the expected answers. `exFused` is an
upper bound: an operator followed by something that isn't an operand is no longer backed out of (the
day's inputs have none; `chainLeft`'s contract says the operator is left unread). It still costs
11.8 K instructions an operation: the operations are cheaper to avoid than to speed up.

## 2. Scan (2024 day 3)

### 2.1 Stages

| Variant | Instructions (G) | Wall (s, loaded) | What it adds |
|---|---:|---:|---|
| read and `toList` (`input.toList.length`) | 2.28 | 0.30 | 0.8% of `main` |
| parse (`parseInstructions`, count them) | 279.35 | 26.9 | **277.1 G net: 99.2%** |
| parse and part 1 (`sumBy .result`) | 279.25 | 23.2 | under 0.1 G |
| both (`main`) | 279.39 | 23.9 | part 2's fold: 0.1 G |

### 2.2 Top functions (whole run, 73,088 samples)

By kind: runtime 30.4%, generated code 26.2%, allocator 22.2%, `sw_*` 20.1%.

| Function | self | note |
|---|---:|---|
| `sw_apply_prepare` | 8.9% | 163.5 M calls |
| `drop_glue::<Value>`, `value::free`, `Fun::take_children`, `Rc<Fun>::drop_slow`, `Fields::drop`, `Rc<[Value]>::drop_slow` | 8.0, 6.8, 3.4, 2.8, 2.7, 1.3% | freeing, 25% together |
| `mi_malloc` / `mi_free` | 6.5% / 6.2% | allocator |
| `sw_eff_step` | 6.4% | 120.0 M steps |
| `apply2`, `apply4`, `apply1` | 3.5, 2.1, 1.1% | |
| `Std.Parse.%elim#95` | 3.3% | the fused `runFrom` state handler |
| `Value::clone`, `rt_loop`, `forwarded`, `state_step` | 2.7, 3.3, 1.3, 1.1% | |

Generated code is 26.2%, of which `Std.Parse*` 10.7%, `Std.List*` 1.6%, `Std.Effect*` 1.4%, the
day's code 1.1%. In program terms (self time, from the profile's frames), `State.note`
is 0.5%: the **handler's** bookkeeping is cheap; section 2.4 shows what is expensive is
performing the `note` operation.

### 2.3 Runtime calls

| | scan |
|---|---:|
| `Parse` operations first performed | 22.43 M (routed: 26.25 M) |
| `sw_eff_step` | 120.0 M |
| `sw_apply_prepare` | 163.5 M (partial application 74.9 M, `DoneK` 22.4 M, closure 22.4 M, `JumpK` 22.4 M, eager resumption 21.3 M) |
| `sw_closure` | 92.0 M |
| `sw_cell_new` plus cache hits | 75.3 M + 54.7 M |
| `Bind` nodes pushed, popped | 40.9 M, 31.3 M |
| forwarding clauses skipped | 21.3 M |
| runtime objects | 142.6 M (6.4 an operation) |
| `TextToList` | 6.02 M |

Operations by kind: `literal` 6.02 M (23%), `note` 5.72 M (22%), `mark` 4.54 M (17%), `reset` 3.82 M
and `stop` 3.82 M (15% each), `span`/`next` 2.34 M (9%). Objects per operation: runtime 6.4,
closures 4.1, generated code's cells 5.8, about 17 in all.

### 2.4 The hot loop in the program's terms

`parseInstructions` is `Parse.all memory (() => findAll instruction)`. Per copy of the input (17,962
characters): 745 instructions (686 `mul`) occupy 8,449 characters, and the other **9,513 characters
(53%) are noise**. `findAll` makes one round per noise character, and a round is:

1. `attempt` (a `mark` and a handler), around `instruction`, which is `oneOf [mul-alternative, pick]`:
2. `optional` (a `mark`, a handler) around `text "mul("`: `literal` fails, `note`, `stop`; the handler
   resets (`reset`).
3. `pick [("do()", Do), ("don't()", Dont)]`: `literal` twice (each with `"do()".toList` built first),
   `noteWords`: `note` twice, `stop`; `attempt`'s handler resets.
4. `next` skips the character.

About 10 operations a noise round (inferred: 22.4 M operations minus about 3 M for the 149 K matches,
over 1.90 M noise rounds), 6 of them the failure of `text` and `pick` that nobody will read. It is
the same story as expressions' brackets: a failure costs as many operations as a success.

Lean's scan does the same loop with `hasAt` (a byte compare, after a `toUTF8` of the word) and no
handlers: its whole run is about 1.7 K instructions a character of input, including the
allocation in `hasAt` (`text.toUTF8` and a `List.range` per try); ours is about 78 K a character.

### 2.5 Scratch variants (same answers: `34992058400 11255120400`)

| Variant | Instructions (G) | Change | Operations | Eff steps |
|---|---:|---:|---:|---:|
| the day's parser (`scBase`) | 279.29 | | 22.43 M | 120.0 M |
| handler ignores `note` (`scQuiet`) | 271.62 | -2.74% | | |
| character lists made once (`scConst2`) | 262.97 | **-5.84%** | 22.43 M | 120.0 M |
| and `pick` notes nothing (`scConst`) | 225.05 | **-19.42%** (the notes: 13.6% of `scBase`) | 18.6 M (est.) | |
| `findAllStarting (c => c == 'm' ∨ c == 'd')` (`scStarting`) | 31.03 | **-88.89%** | 2.10 M routed | 12.4 M |
| both `findAllStarting` and the character lists (`scConst2Starting`) | 30.34 | -89.1% | | |

Cost of a `pick` note: the 38.0 G between `scConst2` and `scConst` is 3.8 M `note` operations
(2 a failing `pick`, 1.9 M failing `pick`s) at **10.0 K instructions each**, the same as the run's
average 12.5 K: a `note` costs as much as any other operation although its handler does almost
nothing (`State.note` self time 0.5%). The cost is the effect machinery: the `Bind` node, the
resumption, the state route, the continuation.

`scStarting` still spends 31.0 G, 5.2x Lean's 5.99 G: 12.4 M effect steps for 180 K attempts
(903 `m`/`d` characters a copy) and 149 K matches, with the same shape of profile (generated code
29.7%, runtime 28.2%, allocator 23.5%). The hot loops left are the matches: `text "mul("; shortNumber()
...` is 4 to 10 operations a match.

## 3. Why Lean is faster

### 3.1 What Lean's versions do

`bench/compare/lean/Compare/Scan.lean` and `Expressions.lean` are not parser-combinator programs:

- Input is a `ByteArray` and the parser state is a `Nat` position passed and returned
  (`Option (Instruction × Nat)`, `Except String (Expression × Nat)`).
- `hasAt` compares bytes at a position; there is no `Mark`, no `State` record, no `Problem` list, no
  handlers. A failed alternative returns `none` and the caller tries the next with the same position:
  backing up is free.
- `shortNumber` and `parseNat` are `while` loops on bytes.

So Lean's parse of a noise character is: `hasAt "mul("`, `hasAt "do()"`, `hasAt "don't()"` and
`position + 1`: three allocations of `toUTF8`, three of `List.range`, and the loop. Lean's whole
programs take 6.09 G (expressions) and 5.99 G (scan) instructions, 660 ms and 582 ms.

### 3.2 What ours does the same work as

| | Lean | native | native / Lean |
|---|---:|---:|---:|
| expressions instructions | 6.09 G | 267.75 G | 44x |
| scan instructions | 5.99 G | 279.39 G | 47x |
| by time (job 34) | | | 68x, 72x |

The time ratio is above the instruction ratio by a third: native's IPC is lower (SW-2432 measured
1.99 and 2.11 against Lean's 2.66 and 2.94) because of its allocation and freeing.

### 3.3 Operations are the unit

The parser's grammar is written as operations that backtrack through handlers. Every operation,
whatever it does (a `note` with a one-word problem, a `mark` of the current place), pays the same
effect cost, 10 K to 17 K instructions. Lean's equivalent of an operation is a function call, tens
of instructions. Section 1.5's and 2.5's gains come from performing fewer of them, not from making
each cheaper.

### 3.4 Why an operation costs 12 K instructions and an object only 100 to 230

SW-2462 and SW-2463 measured what **removing** one object saves: about 100 instructions for a
resumption, 183 to 229 for a cell. An operation builds 17 to 24 objects and takes 5 to 6 effect
steps, so its objects at that rate are 2 to 5 K instructions, a third of the 12 K to 16.6 K. The
rest is what the objects carry with them and the marginal figures don't show: each is also
initialised, passed through `sw_apply_prepare` (127.7 M calls; 7.9% of self time), counted
(`Value::clone` 2.1%) and dropped through `drop_glue`, `take_children` and `free` (23.5% of self
time on expressions). Not separated here. It means a lane that removes an object is measured at
100 to 230 instructions, but one that removes a *whole operation* (all its objects, steps and
applies together) saves 10 K. Hence the order of the ranking.

## 4. Ranked targets

Savings are fractions of the run's instructions, expressions then scan. *measured* means a scratch
variant gave the answers and the instruction count; *estimated* says from what.

1. **`findAllStarting` in day 3: scan -88.9% (measured).** `Parse.findAllStarting` is in std
   (Parse.sw:599; tested, with a Reads lemma at Reads.sw:1978); the day uses `findAll` because it is
   the general one. The parser can only match at an `m` or a `d`, so `findAllStarting (c => c == 'm'
   ∨ c == 'd') instruction` reads the same instructions. Scan goes from 47x to 5.2x Lean in
   instructions. This is a change to the AoC day, not to the compiler. Proofs: `Parse.readsFindAllStarting`
   (Reads.sw:1978) gives the same `Scattered spec` as `readsFindAll` with no side condition (what
   is read is soundly a list of parts of the input); I did not check Day03's `Proofs.sw` (grep finds
   no `findAll` or `parseInstructions` in it or the Spec), and a completeness statement would need
   the condition that `starts` holds at the first character of every instruction. **Caution on over-fitting** (Matt's note on the
   benchmark): this speeds up one program by using the right API, which a user of `Parse` would
   write. It says nothing about the runtime, and the comparison should still show the runtime's gaps
   (use expressions, matcher and the other parsing days for that). Run `task bench:aoc` after: days
   that scan for needles (2024 day 3 only, as far as the greps go) would move.
2. **Cheaper grammar shapes for `oneOf` and `chainLeft` (expressions): -17.8% for one-character
   dispatch, -63.0% with the loop (measured, upper bound).** Two std/library options: (a) a
   `oneOf` whose alternatives carry the characters they can start with (`Parse.oneOfStarting`, as
   `findAllStarting` is to `findAll`), so a failing alternative's `mark`, handler, `note`, `stop`
   and `reset` are not paid for the `(` of every bracket; (b) a `Parse.chainLeft` for operators that
   are literal words (`Parse.chainLeftWords`), which tests the words with `literal` and commits to
   the operand after one. (b) changes `chainLeft`'s back-up after an operator that isn't followed by
   an operand, so it is a new function with a new contract, and the Day18 proofs would use its lemma.
   The upper bound is 99.2 G, 16x Lean in instructions.
3. **`pick`'s failure notes: scan -7% to -13.6%, expressions -3% to -6% (partly measured).** Scan
   measured with the notes dropped: -13.6% (`scConst` against `scConst2`). Cheapest forms: one
   operation noting all the words (`Parse.noteAll`; halves the cost: *estimated* -6.8% scan, -2.9%
   expressions at 10.0 K instructions an operation), or noting nothing until the parse fails and
   rebuilding the expectation then (the `pick` words are known to the runner only if the operation
   carried them: needs a failing `stop` that names them). Expressions: *estimated* from 1.58 M
   `note`s x 10 K = 15.8 G (5.9%) if dropped, half if combined. SW-2337 (done) made the handler's
   bookkeeping cheap; this is the operation, not the handler. Messages must stay the same: the
   parse error tests pin them. Overlaps SW-2327 §2.5 (stage E, which asked for lists once per call
   site too).
4. **Character lists made once: scan -5.8%, expressions -3.9% (measured).** `Parse.text expected`
   and `Parse.pick` call `expected.toList` per try; the scratch variants hold `"mul(".toList` as a
   top-level constant. The std-level fix: `Parse.literal` takes the `Text` (the handler already
   walks the list; `Text.stripPrefixChars` could walk a `Text`'s chars without building a list), or the
   compiler lifts `Text.toList` of a literal to a constant when `text` is inlined at its call site
   (SW-2327's "with B's hoisting", which didn't happen: `TextToList` is still 3.28 M and 6.02 M
   calls). Not on the board; SW-2327 §2.5's second bullet is the same thing.
5. **R4 (SW-2464): -2.9% to -5.0% expressions, -4.0% to -6.9% scan (estimated).** See section 5.
6. **R5 (SW-2465): -1.2% to -1.8% expressions, -1.6% to -2.4% scan (estimated).** See section 5.
7. **R7, rebuilt forwarded operations: -1.2% to -1.5% expressions, -0.4% scan (estimated).**
   17.49 M cells on expressions (22.95 M before R3's change; 0.67 per skipped forward) and 5.25 M on
   scan, at SW-2463's 183 to 229 instructions a removed cell.
8. **Closures (SW-2352, operations in place stage E): not estimated.** 103.9 M `sw_closure` calls on
   expressions (6.5 an operation) and 92.0 M on scan (4.1): `manyFuel`'s round builds eleven
   closures and `Pap`s (23% of its own instructions). The stage builds `bind`'s continuation closure
   only when something suspends. Needs its own measurement.
9. **Compact values (SW-2324 and the compact-values proposal): not estimated.** Objects are
   cheaper but not fewer; the census says what a `Fun` and a cell weigh (SW-2425).

Already done, for the record: SW-2487 (`many` reuses its mark) removed 2.55 M of 18.65 M operations
(14%) from expressions' first count (18.65 M to 16.10 M); SW-2486 (a fused `token nat`) is in review
and does not touch these two programs (`nat`, not `token nat`). SW-2352, SW-2402 and SW-2403 are
open operations-in-place work (the last two for open rows and the skip table).

## 5. R4 and R5 re-estimated

Method (*estimated*): today's counts from section 1.3 and 2.3, times the measured cost per removed
object from SW-2462 and SW-2463: **about 100 instructions per resumption, 183 (R3) to 229 (R2) per
cell**, and, where a step or an apply goes too, 100 to 150 an apply and 100 a step (not measured:
the lanes kept step counts, so no figure for a step exists; these are guesses and are the high end).

**R4** removes, per perform whose `bind` takes a fresh `Call o DoneK` (all of them; no `Call` was
shared, the stage 0 finding, still true: 17.51 M of 17.51 M on expressions, 26.25 M of 26.25 M on
scan):

| Per run | expressions | scan |
|---|---:|---:|
| `Bind` nodes (= pending cells after R2) | 17.51 M | 26.25 M |
| `Done` cells from `DoneK` | 16.10 M | 22.43 M |
| `DoneK` applies (`sw_apply_prepare`) | 16.10 M | 22.43 M |
| pushes and pops of that `bind` | 17.51 M + 16.10 M | 26.25 M + 22.43 M |
| cells at 183 to 229 | 6.15 to 7.70 G | 8.91 to 11.15 G |
| `DoneK` applies at 100 to 150 | 1.61 to 2.42 G | 2.24 to 3.36 G |
| steps (pushes and pops) at 0 to 100 | 0 to 3.36 G | 0 to 4.87 G |
| **total** | **7.8 to 13.5 G** | **11.2 to 19.4 G** |
| share of the run (267.75 G; 279.39 G) | **2.9% to 5.0%** | **4.0% to 6.9%** |

The low end counts only the cells and the applies; the high end adds the push and pop steps. The
proposal's 2.3 to 3.2% and 2.8 to 3.9% (after R2) were at the low end of this, because they used
140 an object. Central: 3.8% and 5%. Effect and step counts change (`pushes` and `pops` fall by
33.6 M and 48.7 M, `sw_eff_step` by about a quarter on expressions), as the proposal said (D3437).
The 23.77 M (expressions) and 14.65 M (scan) `bind`s of a `Bind` node, the do-block ones, stay.

**R5** removes, per state route (16.10 M on expressions, 22.43 M on scan), the `StateK` resumption
and the `Jumped` object (two objects now R1 has merged the `Rc<Resume>`), and the `JumpK` apply:

| Per run | expressions | scan |
|---|---:|---:|
| `StateK` and `Jumped` at 100 each | 3.22 G | 4.49 G |
| `JumpK` apply at 0 to 100 | 0 to 1.61 G | 0 to 2.24 G |
| **total** | **3.2 to 4.8 G** | **4.5 to 6.7 G** |
| share of the run | **1.2% to 1.8%** | **1.6% to 2.4%** |

The proposal's 1.7 to 2.0% and 2.1 to 2.6% (after R1) were with three objects a route; R1 merged one
before R5, so the new figure is lower. R4 and R5 together: about 4.1% to 6.8% on expressions and 5.6%
to 9.3% on scan (the high ends add steps and applies that haven't been measured separately). Neither
is on the path that closes the gap: since an operation costs about the same whatever it does,
the same saving is dropping 4 to 9% of the operations, which section 4's items 1 to 3 do many times
over.

## 6. Reproducing

All from the worktree. The stage and variant sources were scratch files in the AoC project
(`aoc/src/Scratch/Stages.sw`, `Variants.sw`) and are not committed; the lines that matter:

```
-- scan: the whole change
findAllStarting (c => c == 'm' ∨ c == 'd') instruction
-- expressions: the operand by one character, and the chain as a loop
match Parse.next (c => c == '(') with
  | Some c => (let inner := expression(); Parse.char ')'; Parenthesised inner)
  | None => Number Parse.nat()
-- chainLoop: match operators.find (o => Parse.literal o.chars) with
--   Some o => chainLoop (Operation o left term()) | None => left   (fuel from Parse.mark().left)
```

```
nix develop -c task profile:native -- expressions scan --by-instruction --bodies 12 --top 25
   # 5 min each cap; builds in target/bench, recordings in target/profile/NAME.json.gz
python3 -I dev/profile_top.py target/profile/expressions.json.gz --top 40 --group Std.Parse --group Std.List
cd aoc && ../target/bench/release/stitchwort build --native Scratch.Variants.scStarting -o PROG
/usr/bin/time -l PROG < INPUT        # "instructions retired"
STITCHWORT_RUNTIME=.../target/profiling/release/libstitchwort_standalone.a \
  stitchwort build --native --count-bodies Scratch.Variants.NAME -o PROG-counts
STITCHWORT_CALL_COUNTS=1 PROG-counts < INPUT > /dev/null
```

Inputs: `bench/compare/compare.py`'s `lines` scaling by hand: the real file joined by `\n` 180 times
(expressions) and 200 times (scan). Run times: profile build 3 min; each scratch build and run
under 30 s unloaded.

## 7. What I didn't do, and what I'm unsure of

- **Not done:** R4, R5 or any of the ranked changes themselves (measurement only); the value
  census (`value-census` build) for these two (the objects per operation above are from
  `call-counts`, which counts runtime sites and generated code's `sw_cell_new`, not every
  allocation); a profile of `exFused` and `scStarting` beyond the kinds split, so what remains in
  them is not broken down; the Day03 and Day18 proofs against the scratch grammars.
- **Uncertain:** (1) the per-step and per-apply costs in section 5 are guesses; only the per-cell
  (183 to 229) and per-resumption (100) figures are measured. R4 is the most uncertain: if
  a removed push and pop is free the low end stands. (2) Section 3.4's gap between 12 K an
  operation and 2 to 5 K from objects is not explained here. (3) The wall times were under load 7
  to 39 and aren't a rate; instruction counts are not affected by load but a 3% difference between
  this build (non-incremental, no kache) and job 34's is expected. (4) `exFused` changes `chainLeft`'s
  back-up contract and `exOperand` changes the `oneOf`: both give the same answers on the real
  input, which has no case where the difference shows. (5) "10 operations a noise round" is
  inferred, not counted per construct; per-construct counters would settle the split of
  operations (`Parse` operations by call site).
- **Machine:** shared with other lanes, so one run of each; the instruction counts repeat to better
  than 0.1% (SW-2462, SW-2463) and are what the comparison uses.
