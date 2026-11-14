# What one `Parse` operation costs, and where to cut (SW-2493)

SW-2493, 9 Nov 2026, Opus, `lane/SW-2493` from `main` at `a53b0b5b3` (after SW-2487, SW-2491
and effect-runtime R1-R3). Measurement and write-up only: no compiler, runtime or std code
changed. It answers SW-2492 §3.4 (docs/reviews/SW-2492-expressions-scan-profiles.md): why does
one `Std.Parse` operation cost 12-17 K native instructions when removing one effect-runtime object
saves only 100-230?

**How to read the numbers.** The unit is **instructions retired** (`/usr/bin/time -l`), which
repeats to better than 0.1% and is what the comparison uses. **Measured** means a native build was
run and counted; **from shares** means a samply time share multiplied by a measured instruction
total (this assumes the same instructions per cycle across functions, so treat it as ±30%);
**inferred** means worked out from measured numbers; **estimated** says how. Builds are this
worktree's `target/release/stitchwort` (kache, not `target/bench`), so absolute totals may differ
from job 34's by a few percent; ratios and per-operation costs are what matter here.

## 0. Summary

**The problem.** Natively, `expressions` takes 237.7 G instructions (after tonight's SW-2491) and
`scan` 279.3 G, 17.5 K and 12.5 K per `Parse` operation performed. Lean does each program in about
6 G.

**What one operation costs, measured with scratch programs** that perform N operations under k
handlers and fit cost = a + b·k (§2):

| | per operation |
|---|---:|
| a pure loop turn (for scale) | 49 |
| a one-operation user ability, one-clause `Nat` state handler, no other handler (`Tick.tick`) | **5,680** |
| `Parse.mark` under `runFrom` alone | 6,800 |
| `Parse.literal` (fails / succeeds), `reset`, `note`, `next`, `span` | 7,470 / 8,730, 7,720, 8,540, 8,920, 9,160 |
| each forwarding handler (`optional`, `attempt`, `label`, `sectionLine`) the operation passes | **+1,430 to +2,070** |
| starting and ending one `optional` (`h`) | 5,650 |
| a failing `stop` caught by `optional` (route and dropped continuation, beyond its operations) | about 3,000 (inferred) |
| one more `bind` of a sub-parser's computation (`e`) | 1,230 |

The fit is linear to 1% (mark under 0 to 6 `optional`s: 6,803, 8,977, 10,970, 13,034, 15,120,
19,213). **The base cost `a` is the big term, not the depth:** a typical operation passes 1.75
forwarders on expressions and 0.95 on scan, about 3.0 K and 1.5 K, while `a` is 6.8 to 9.2 K. And
`a` is nearly all generic effect machinery: an ability with one operation and a `Nat` state
already costs 5.7 K, 116 times a loop turn; `Std.Parse` adds 1.1 to 3.5 K (the eight-clause
dispatch, the `State` record, the clause's own work).

**The two programs, accounted (§5):** the model explains 84% of expressions and 92% of scan.

| per operation performed | expressions | scan |
|---|---:|---:|
| the operations at `runFrom` (`a` by kind) | 8.1 K | 8.4 K |
| forwards through `optional`/`attempt` | 3.0 K (2.5-3.6) | 1.5 K |
| handler starts (`optional`, `attempt`) | 2.0 K | 1.0 K |
| binds of sub-parsers beyond the perform's own | 1.5 K | 0.6 K |
| not modelled: the parsers' own work, line splitting, evaluation | 2.9 K | 1.0 K |
| **total (measured)** | **17.5 K** | **12.5 K** |

A check against an independent measurement: SW-2492 removed 3.8 M `note`s from scan and saved
10.0 K each; the model gives a `note` one handler deep 8,540 + 1,430 = 9,970.

**Why removing one object saves only 100-230 (§6):** that figure is right; an operation is simply
many things at once. At the floor (`Tick`, 5.7 K) it is about 10 allocations and frees (2.1 K), 6
calls through the generic apply path `sw_apply_prepare` and its stubs (2.0 K), 3 effect-loop
steps (0.8 K), a state step and the generated code. Of the 5.7 K, 1.85 K is the handler clause
being reached through two partial applications (`handlePlus`, then `%elim` holding all eight
clauses, which are copied and dropped on every operation) and a `JumpK` apply. On top of the floor
come the program's forwards, handler starts and extra binds.

**The cut, ranked (§7).** Savings are of the whole run's instructions, expressions / scan, all
**estimated** from the measured component costs and today's counts:

| # | Option | Expressions | Scan | Changes counts or behaviour? |
|---|---|---:|---:|---|
| 1 | Operations in place natively (stages C-D of operations-in-place.md, with forwarders skipped at lookup) | **-42 to -62%** | **-46 to -68%** | effect and step counts (D3412 accepted this); results no. **Revisits D3430: Matt's** |
| 2 | Compiled handler dispatch: one dispatch closure per handler, the clause reached by the operation's tag, no `handlePlus`/`%elim` partial applications | -9 to -12% | -11 to -14% | no (internal apply counts only). Design note warranted |
| 3 | R4 (SW-2464): `bind (Call o DoneK) k` is `Call o k` | -4 to -8% | -6 to -11% | step counts (D3437 accepted) |
| 4 | Capture-free lambdas built once, as constants (measured 159 instructions each) | -3.5 to -3.9% | -2.6 to -3.1% | no; every program gains |
| 5 | Cheaper forwards: resumption fields moved, not copied, when unique; R7's rebuilt operations | -3 to -5% | -2 to -4% | no |
| 6 | A state clause's jump without a `Jumped` object or a `JumpK` apply | -2.3 to -3.1% | -3.2 to -4.4% | no |
| 7 | A smaller `Parse.State` | under 1% | under 1% | no |
| 8 | Library: choice points kept in `runFrom`'s state instead of nested handlers | -11 to -18% (very uncertain) | less | effect counts, proofs; conflicts with 1. Not recommended unless 1 is refused |

Options 2 to 6 are local and together come to roughly 25-35% (1.3-1.5×); they don't add exactly.
Option 1 is the only one that removes the floor itself: an emulation of an operation run in place
(the handler's step called directly, the rest of the loop a closure given the answer) costs 340
instructions for `Tick` and 3.4 K for `next`, against 5.7 K and 8.9 K now.

**Decisions for Matt** (§8): whether to reopen operations in place for native code (D3430
dropped it on an estimated 1.3× ceiling that counted allocation and freeing as not the effect
machinery's; this note measures that most of that allocation is the machinery's), and whether
option 2 gets a design note. Options 3 to 6 are runtime- or compiler-internal and change nothing a
user sees.

## 1. Method

- **Scratch programs** (`Ops.sw`, kept in the scratchpad, not committed; the lines that matter are
  in §9): a loop of N operations of one kind (`mark`, `next`, `literal`, `span`, `note`, `reset`)
  under `Parse.run` of N characters, wrapped in k nested `optional`, `attempt`, `label`,
  `labelWhole` or `sectionLine`; loops with one `optional` per turn, succeeding or failing; a loop
  that calls a sub-parser; a user ability `Tick` with one operation and a one-clause `Nat` state
  handler, with k nested forwarding handlers; an eight-operation ability; and emulations of an
  operation run in place. Cost per operation = (instructions at N − instructions at 0) / N, at N
  from 100,000 to 5,000,000 (linear: `tick` gave 5,681, 5,683 and 5,683 at 0.1 M, 1 M and 3 M).
- **Counts:** the `call-counts` runtime and `--count-bodies` on the scratch program and on both
  benchmarks at a tenth of the comparison's input (instructions scale linearly: 23.74 G and
  27.95 G at a tenth, 237.75 G and 279.33 G at full size). Counts below are the tenth's times ten.
- **Profiles:** samply at 8 kHz on `tick` (18,052 samples), `mark` alone (16,856) and `mark`
  under four `optional`s (19,652), summarised with `dev/profile_top.py` and grouped by function
  kind; `--pc-map` for the bytecode of the generated bodies.
- **Reading the code:** `crates/rt/src/native_abi.rs` (`sw_eff_step`, `sw_apply_prepare`,
  `sw_state_step`, `sw_resume_begin`, `sw_bind`, `sw_closure`), `crates/rt/src/effect.rs`,
  `crates/elab/src/std/Parse/Parse.sw`, and the generated bytecode from the pc-map.

## 2. The fitted model

### 2.1 Depth

Every forwarding handler of `Std.Parse` (`optional`, `attempt`, `label`, `sectionLine`: their
clauses for the reading operations only re-perform and resume) costs the same per level, linear
in the depth (**measured**):

| operation | depth 0 | depth 2 | per level |
|---|---:|---:|---:|
| `mark` (also 1, 3, 4, 6 levels: 8,977 / 13,034 / 15,120 / 19,213) | 6,803 | 10,970 | 2,070 |
| `next` | 8,915 | 11,820 | 1,450 |
| `literal` (succeeds) | 8,726 | 11,608 | 1,440 |
| `span` | 9,164 | 12,024 | 1,430 |
| `reset` | 7,721 | 10,585 | 1,430 |
| `note` | 8,541 | 11,405 | 1,430 |
| `Tick.tick` through a user forwarding handler (1, 2, 4 levels: 7,838 / 9,765 / 13,725) | 5,683 | 9,765 | 2,010 |
| `mark` under `attempt` / `sectionLine` / `label` | | 10,970 / 10,864 / 10,863 | about 2,050 |

So **cost ≈ a(kind) + 1.43 to 2.07 K × forwarders passed**. (`mark`'s forward is dearer than the
others'; not chased.)

Two handlers aren't forwarders, and are dearer (**measured**): `label` routes `note` to its own
clause, which performs a `mark`: a `note` under two `label`s costs 18,502, about 5 K a level.
`labelWhole` is a state-passing fold whose every clause runs: `mark` costs 15,932 under one and
24,545 under two (about 9 K a level), and `next` under two costs 51,767, because each level's
reading clause performs a `mark` of its own (`Parse.further`), which the levels outside it then
handle too: an operation at depth d becomes 2^d − 1 operations at `runFrom`. Neither occurs in
the two benchmarks (`blankLine` uses `labelWhole`; sections nest it rarely). Worth a small ticket
(§10).

### 2.2 How deep is the stack at a typical operation?

Forwards per operation performed (**measured**, routed forwards over first performs): **1.75 on
expressions** (23.66 M forwards, 13.56 M operations) and **0.95 on scan** (21.25 M, 22.43 M).
From the grammars (**read**): expressions' `chainLeft` runs `many`, whose every round wraps the
operator and operand in `optionalFrom` (one level); the operand is `oneOf [nat, bracket]`, whose
first alternative runs under another `optional` (two levels for the number's `span`); part 2's
second precedence level nests a `many` round inside a `many` round (three to four for a number);
a bracket's inner expression adds the same again. Scan's noise character runs under `findAll`'s
`attempt` (one level: `pick`'s two `literal`s and two `note`s), and `oneOf`'s `optional` around
`text "mul("` (two levels: that `literal` and `note`); `findAll`'s own `mark` and `next` are at
depth 0. So a typical operation is one to three forwarders deep, and depth costs 1.5 to 3.0 K an
operation, a fifth of the total at most.

### 2.3 Handler starts, failures, binds

| scratch loop (per turn) | measured | what it adds |
|---|---:|---|
| `optional (() => next)`, succeeding | 23,446 | its operations are `mark` (6.80 K) and `next` one level deep (8.92 + 1.45 K): **h = 5.65 K** for the handler's start and end |
| `optional (() => satisfy "a digit" (c => False))`, failing | 42,125 | `mark`, `next` and `note` one deep, `reset`, h: **about 3.0 K** left for `stop`'s route to `optional`'s clause and the continuation it drops (inferred) |
| `let x := markPlus(); …` (a sub-parser that performs, then computes) | 8,029 | one more `bind`: **e = 1.23 K** (a `Bind` node, a push and a pop, a closure and its apply) |

**What a handler start builds (read, from the bytecode of `Parse.optional/lambda38`):** nine
`Closure` instructions with no captures (the clauses for `span`, `next`, `literal`, `mark`, `reset`,
`note`, `fatal`, the return clause and the forwarder), one capturing `start` (the `stop` clause),
a partial application of `%elim` holding all eight clauses, one of `handlePlus`, an `Apply` for the
forwarding map, then `sw_eff_begin` (an `Rc<Handler>`) and a new run loop. The counts agree: an
`optional` round builds 14 closures and 2 partial applications, against 4 closures for its two
operations. `manyFrom`, which inlines `optionalFrom`, builds the same per round.

## 3. One operation followed through

### 3.1 The floor: `Tick.tick` under a state handler, 5.68 K

What happens, in order (**read**, `native_abi.rs` and the bytecode), with each step's share of
the profile turned into instructions (**from shares**, of 5,680):

| step | what is built or called | share | instructions |
|---|---|---:|---:|
| 1. perform, in generated code (`tickLoop`) | three cells (the operation, its injection, `Call o DoneK`); the continuation closure (two captures); `sw_bind` makes a `Bind` node | 7.9% | 450 |
| 2. the loop meets `Bind`, `Call`, then `Done` (`sw_eff_step` ×3) | push (R2 reuses the node), split the `Call`, make the `StateK` resumption; pop | 14.5% | 820 |
| 3. reach and run the clause (`apply4` from the loop) | `call o k jump s` applied: `sw_apply_prepare` on the `handlePlus` partial application (copies its two held values, over-applies), `handlePlus` switches on `L`/`R` and applies `fl o k`: `sw_apply_prepare` on the `%elim` partial application (copies every held clause), `%elim` switches and applies the clause; the clause's `k y s′` is an apply of `JumpK`, which makes a `Fun::Jumped` | 32.6% | 1,850 |
| 4. `sw_state_step` | takes the `Jumped` and the `StateK` apart, frees them | 5.6% | 320 |
| 5. `rest y`, `rest` = `DoneK` (`apply1`) | `sw_apply_prepare`'s `DoneK` path makes a `Done` cell | 11.4% | 650 |
| 6. apply the popped continuation (`apply2`), its body (`tickLoop/lambda157`) | apply through a cold cache to `sw_apply_prepare`, unpack the captures, tail call | 10.3% | 590 |
| 7. the loop's own code, frees outside the above | | 5.8% | 330 |
| not placed (nested loops make inclusive times overlap) | | 11.9% | 670 |

By kind of code (**from shares**): the apply machinery 34.8% (2.0 K), freeing and reference
counts 19.5% (1.1 K), the allocator 17.2% (1.0 K), the effect loop 15.8% (0.9 K), generated code
10.7% (0.6 K). Counted per operation (**measured**): 6 `sw_apply_prepare` (3 partial applications,
1 closure, 1 `DoneK`, 1 `JumpK`), 3 `sw_eff_step`, 1 `sw_state_step`, 1 `sw_bind`, 1 closure, 1
generated cell plus 2 from the cell cache, and the runtime's `Bind` node, `Done` cell, `StateK` and
`Jumped`: about ten allocations and frees, at about 200 each.

So the floor is not one expensive thing. It is ten objects (2.1 K), ten calls through generic
paths (2.0 K), three loop steps (0.8 K) and the code around them. The single largest piece, step 3,
is the clause being reached by two partial applications rather than a call.

### 3.2 What `Std.Parse` adds: 1.1 to 3.5 K

- **The dispatch's width, 0.47 K (measured):** the same loop with an eight-operation ability
  costs 6,144 against `Tick`'s 5,674. `%elim`'s partial application holds every clause, and
  `sw_apply_prepare` copies all of them into the call and the callee drops the seven it doesn't
  use: about fifteen reference-count operations per operation.
- **The `State` record and the clause shapes, about 0.65 K for `mark` (inferred):** `mark` is
  6,800, 1.13 K over `Tick`, less the width.
- **The clause's own work, 0.7 to 2.4 K over `mark` (measured differences):** `next` (8.92 K)
  applies the test through a closure, matches the list, builds `Some char` and advances the state;
  `span` (9.16 K) builds the run as a list and counts it (`lengthOnto`); `literal` compares the
  prefix (`stripPrefixChars`) and counts the word; `note` conses the problem (`State.note`);
  `reset` rebuilds the state with the mark.

**What `State` looks like and how much a step copies (read):** `State = { at: Mark, furthest,
expected, messages }` with `Mark = { rest, offset, left }`, seven words in two cells. An advancing
operation makes a new `Mark` and a new `State` (`State.advance`, compiled with a `[reuse]`
variant that writes in place when the old cells are unique); `mark` hands out `state.at` shared,
so the next advance after a `mark` can't reuse the `Mark` cell and builds one. That is at most two
cells, 0.2 to 0.4 K, on an advancing operation, and nothing on the others: a few percent of an
operation. A flatter `State` would make `mark` build a cell every time (42% of expressions'
operations are `mark`s) to save one on an advance, so it isn't a win.

### 3.3 A forward: 1.43 to 2.07 K a level

The profile of `mark` under four `optional`s against `mark` alone, per level (**from shares**,
(15,120 − 6,803) / 4 = 2,080): effect loop +0.81 K, freeing +0.58 K, allocation +0.40 K, apply
+0.23 K. What happens (**read**): the inner fold's loop meets the `Call`, finds the clause in its
forwards table (stage B), makes an eager `Fun::Resume` and a `Call o r` (reusing the cell, R3;
rebuilding the operation's injection about half the time, R7) and returns it as its value; the loop
outside handles it as before; when that loop resumes with `rest y`, `rest` is the eager resumption,
so `sw_apply_prepare` → `rt_resume` → `sw_resume_begin` copies the handler, the pending list and
`rest` (new references, even when the resumption is unique) and a new run loop starts, which takes
`Done y` and pops the continuation. Two more loop steps, a resumption object, a loop entered and
left, per level.

### 3.4 Run in place, emulated

The same loops written without the effect runtime, the handler's step called directly
(**measured**):

| emulation | per operation | against |
|---|---:|---|
| `Tick`: the clause called through a function value, answer and state returned in a record | 342 | 5,683 |
| the same, the rest of the loop a closure applied by an unknown function | 1,595 | |
| `next`: `Parse.State.next` called directly, the rest of the loop a four-capture closure | 3,651 | 8,915 |

So running the step in place keeps the clause's own work and bind's closure and loses the rest:
5.2 K of `next`'s 8.9 K, 5.3 K of `Tick`'s 5.7 K. A one-capture closure built and applied costs 318
(`clos1` − `clos0`), a capture-free one 159 (`next` with a lambda against a global function).

## 4. The objects per operation, reconciled

SW-2492 counted 17 to 24 objects per operation. On expressions today (**measured**, per
operation first performed): closures 6.9, the runtime's objects 8.8 (`Bind` nodes 2.7, `Done`
1.0, `StateK` 1.0, `Jumped` 1.0, skip resumptions 1.75, fold resumptions 0.1, handlers 0.35,
rebuilt operations 0.9), generated code's cells about 8.5, partial applications 0.8. About 60% of
the closures are capture-free (§7.4). Each allocation and free is about 200 instructions, so the
objects are about 5 K of the 17.5 K; the calls that make, apply and take them apart are most of the
rest.

## 5. The two programs, accounted

Full-size counts (a tenth's ×10), multiplied by §2's costs. "a by kind" uses the depth-0 cost of
each kind; `literal` takes the failing and succeeding mid-point (7.6 K on scan, where most fail;
8.1 K on expressions); "stop" is the inferred 3.0 K.

**Expressions** (237.75 G, 13.56 M operations first performed, 14.96 M routed):

| component | count | unit | G | share |
|---|---:|---:|---:|---:|
| `mark` at `runFrom` | 4.75 M | 6.80 K | 32.3 | |
| `literal` | 3.15 M | 8.1 K | 25.5 | |
| `span` / `next` | 2.61 M | 9.0 K | 23.5 | |
| `note` | 1.64 M | 8.54 K | 14.0 | |
| `reset` | 1.41 M | 7.72 K | 10.9 | |
| `stop` (route to `optional`) | 1.41 M | 3.0 K | 4.2 | |
| **operations** | | | **110.4** | **46%** |
| forwards | 23.66 M | 1.43-2.07 K | 33.8-49.0 (41.4) | 17% |
| handler starts (`optional`) | 4.75 M | 5.65 K | 26.8 | 11% |
| binds of sub-parsers, beyond those in h | 16.5 M | 1.23 K | 20.3 | 9% |
| **modelled** | | | **199** | **84%** |
| not modelled | | | 38.9 | 16% |

The 16% left is the parsers' own code between operations (`pick`'s `List.find` and
`TextToList`, `operator`'s `map`, `Nat.fromDigits`, the combinators' closures), splitting lines
(about 1%) and evaluation (under 1%).

**Scan** (279.33 G, 22.43 M operations first performed, 26.25 M routed):

| component | count | unit | G | share |
|---|---:|---:|---:|---:|
| `literal` | 6.02 M | 7.6 K | 45.7 | |
| `note` | 5.72 M | 8.54 K | 48.8 | |
| `mark` | 4.54 M | 6.80 K | 30.9 | |
| `reset` | 3.82 M | 7.72 K | 29.5 | |
| `stop` | 3.82 M | 3.0 K | 11.5 | |
| `span` / `next` | 2.34 M | 9.0 K | 21.0 | |
| **operations** | | | **187.4** | **67%** |
| forwards | 21.25 M | 1.43-2.07 K | 30.4-44.0 (33) | 12% |
| handler starts (`attempt`, `optional`) | 4.10 M | 5.65 K | 23.2 | 8% |
| binds beyond those in h | 10.6 M | 1.23 K | 13.0 | 5% |
| **modelled** | | | **256.6** | **92%** |
| not modelled | | | 22.7 | 8% |

## 6. Why 12-17 K an operation, when an object saves 100-230

The marginal figures (SW-2462, SW-2463: about 100 for a resumption, 183 to 229 for a cell) are
consistent with this note: an allocation and free here is about 200. The gap is that an operation
is many things, not that each is dear:

1. **The floor, 5.7 K:** ten objects, six generic applies, three loop steps, a state step, for an
   operation whose handler does nothing (§3.1). The largest single piece (1.85 K) is reaching the
   clause through two partial applications and a `JumpK`.
2. **`Std.Parse`'s handler, 1.1 to 3.5 K more:** an eight-clause dispatch that copies every clause
   per operation, the `State` record, and the reading itself (§3.2).
3. **The program's share of handler work, 4 to 7 K an operation on expressions, 3 K on scan:**
   1.75 forwards (3.0 K), 0.35 handler starts (2.0 K) and 1.2 extra binds (1.5 K) per operation on
   expressions (§5).
4. **The parsers' own code, 1 to 3 K** (§5's unmodelled part).

Removing one object from step 1 saves its 200. Removing the operation saves all four.

## 7. The cut, ranked

Each saving is the measured component cost times today's full-size counts; the ranges carry the
uncertainty of the component costs (shares are ±30%). Overlaps are noted: the savings don't add.

### 7.1 Operations in place natively: -42 to -62% (expressions), -46 to -68% (scan)

**What:** stages C and D of operations-in-place.md (SW-2339) for native code: at a perform, look up
the handler on a stack of entries, skip forwarders, and when the clause is tail-resumptive (all of
`runFrom`'s but `stop` and `fatal`), call it there with the state and return its answer; anything
else takes today's path. Stage C was built for the machine (branch `lane/SW-2350`, `901a93884`,
kept as the record) with the consumer link that makes it sound.

**Estimate:** per operation at `runFrom`, saving 4 to 6 K (the floor less what stays: the
operation's cells, the lookup, the clause, bind's closure; §3.4's emulations keep 0.3 to 3.7 K;
the low end is with today's dispatch through partial applications, the high end with 7.2's); per
forward 1.3 to 2.0 K; per extra bind 0.75 to 0.9 K (a sub-parser that didn't suspend returns
`Done`, and `bind (Done v) k` already takes `sw_bind`'s fast path, keeping only the closure).
Expressions: 13.55 M × 4-6 K + 23.66 M × 1.3-2.0 K + 21.2 M × 0.75-0.9 K = 101 to 147 G of 237.75 G.
Scan: 22.43 M × 4-6 K + 21.25 M × 1.3-2.0 K + 14.65 M × 0.75-0.9 K = 129 to 191 G of 279.33 G.
`stop`'s 1.41 M and 3.82 M routes keep today's path. That is about 1.7× to 2.6× on expressions
and 1.9× to 3.2× on scan; it would take the programs from 39× and 47× Lean in instructions (6.09 G
and 5.99 G) to about 15-22× and 15-25×.

**Why this differs from D3430's 1.3× ceiling:** SW-2417 split the profile into "effect loop and
leaves" (12%), "apply" (17-19%) and "allocation, freeing, cloning" (51-53%), and bounded stage D by
the first two. But the scratch programs show the allocation is the effect machinery's own: `Tick`
has no work of its own, and its operation is 5.7 K, 37% of it allocating and freeing (§3.1); run
in place it is 342. And stage C's measured 1.04-1.11× was on the machine, where each step's
interpretive overhead dilutes the effect runtime's share; natively the effect runtime is most of
the run.

**What it changes:** effect and step counts (D3412 accepted this for stages B-D); no results, no
messages, no proofs or hashes (the runtimes only). **Risk:** the consumer link (computations as
values) is the soundness condition; stage C answered it on the machine. **Cost:** large (the
native half of stage D was never designed in detail; the stage C branch has the machine half).
**First step if reopened:** a native spike on `Tick` alone, go/no-go at under 1.5 K an operation
(from 5.7 K).

### 7.2 Compiled handler dispatch: -9 to -12% / -11 to -14%

**What:** compile each `handle` so that its clauses are one dispatch function, `(o, k, jump, s)`
switching on the operation's tag and running the clause inline, holding the handler's captures
once; the runtime's `Handler` keeps that function's code and environment and calls it directly at
a route. Today a route applies `handlePlus elim forward` (a partial application) which applies
`%elim c1 … c8` (another, copying all eight clauses) which applies the clause.

**Estimate:** per route, 0.9 to 1.2 K of §3.1's 1.85 K step 3 (the two partial applications, two
switches and fifteen reference-count operations; the clause and its jump stay); per handler start,
1.5 to 2 K (one closure instead of ten, no partial applications). Expressions: 14.96 M routes ×
0.9-1.2 K + 4.75 M starts × 1.5-2 K = 20.6 to 27.5 G. Scan: 26.25 M × 0.9-1.2 K + 4.10 M ×
1.5-2 K = 29.8 to 39.7 G. Every effectful program gains; more for handlers with many clauses.

**What it changes:** nothing a user sees; effect counts unchanged; `sw_apply_prepare` counts fall.
**Cost:** medium, and it touches how handlers are lowered (elaboration's `handlePlus`/`%elim`
shape, the fused state handler, stage B's forwards tables, the JS runtime's lowering), so it
warrants a **design note** before a lane. It is also what makes 7.1's residual cheap.

### 7.3 R4 (SW-2464): -4 to -8% / -6 to -11%

`bind (Call o DoneK) k` becomes `Call o k`: no `Bind` node, push, pop, `DoneK` apply or `Done`
cell for a bound perform. Per perform 0.6 to 1.2 K (from §3.1: a `Bind` node 0.2 K, two of the
three loop steps 0.55 K, the `DoneK` apply and `Done` cell up to 0.65 K; the low end assumes the
loop steps are cheaper than their share). 14.96 M and 26.25 M bound performs. This is above
SW-2492 §5's 2.9-5.0% and 4.0-6.9%, which guessed 0-100 per step and 100-150 per apply; the
profile puts a step at about 275 and the `DoneK` path at up to 650 with its cell. Step counts
change (D3437 accepted). Overlaps 7.1 (in place, the perform isn't bound at all).

### 7.4 Capture-free lambdas as constants: -3.5 to -3.9% / -2.6 to -3.1%

A `Closure` instruction with no captures allocates a new `Fun` every time it runs: `optional`'s
nine clause closures, `Parse.isDigit`-style tests written as lambdas, `() => …` thunks with nothing
free. A closed lambda can be built once and shared, as hoist.rs already does for closed `SigMap`s;
functions are immutable values, so sharing one is unobservable. **Measured:** one fewer
capture-free closure per operation saved 159 instructions (`next (c => True)` 8,906 against
`next yes` 8,747). **Count (estimated):** in the bodies that the counts list (the top 40 by
entries), the `Closure` instructions with no captures times their entries come to 5.8 M of 9.2 M on
expressions' tenth and 6.7 M of 11.2 M on scan's (static: a branch not taken is counted, so these
are upper bounds); taking 55-62% and 50-60% of the measured 93.7 M and 92.0 M closures gives 8.3
to 9.2 G and 7.3 to 8.8 G. Every program that passes lambdas gains. Closed partial applications
of closed functions could follow (in `optional` the `%elim` one holds the `stop` clause, which
captures `start`, so it stays). **Cost:** small (lowering; Sonnet). No semantics change.

### 7.5 Cheaper forwards: -3 to -5% / -2 to -4%

`sw_resume_begin` clones the handler, pending list and `rest` out of an eager resumption even when
the resumption is unique (always, for a one-shot forward); moving them saves three increments and
three decrements, and the resumption is freed sooner. R7 (SW-2492 §4.7: rebuilt forwarded
operations, 0.5 cells per forward on expressions) is the other part. **Estimate:** 0.3 to 0.5 K
of the 1.43-2.07 K per forward (from §3.3's freeing and allocation shares), times 23.66 M and
21.25 M. Runtime-local; no count changes. Overlaps 7.1 entirely.

### 7.6 A jump without an object: -2.3 to -3.1% / -3.2 to -4.4%

A state clause's tail `k y s′` applies `JumpK` (a `sw_apply_prepare`), which makes a
`Fun::Jumped(y, s′)` that `sw_state_step` takes apart at once. Returning the pair in the context
(or a recycled jump) saves 0.4 to 0.55 K per state route (the apply, the allocation and free, part
of the state step; §3.1), times 13.56 M and 22.43 M. Close to R5 (SW-2465), which removes the
resumption only for handlers that never mention `k`, and so doesn't reach `runFrom`. Overlaps 7.1.

### 7.7 A smaller `State`: under 1%

§3.2: the record costs at most two cells on an advancing operation, and flattening it costs a cell
on every `mark`. Dropping `left` (used for fuel and the end test) saves a subtraction. Not worth a
lane on these two programs.

### 7.8 Library: choice points in `runFrom` instead of nested handlers (not recommended)

`optional` and `attempt` could be operations of the one state handler: `choice` stores its
resumption in the state and goes on with `True`; `stop` resumes the newest stored one with
`False`; success pops it (`commit`). That removes every forward and handler start (expressions:
33.8-49.0 G and 26.8 G) but makes each choice a stored, twice-resumed continuation and adds a
`commit` per success. Net, very roughly, 11-18% on expressions (estimated: about 9 K per `choice`
and 7 K per `commit` against what they replace), less on scan. It changes effect counts, makes
`Std.Parse` depend on resuming a continuation twice, means rewriting Parse/Reads.sw's lemmas about
`optionalFrom` and `attemptFrom`, and gains nothing once 7.1 is in (forwards then cost little).
Listed so the option is on record; I'd take it only if 7.1 stays dropped and 7.2-7.6 are done.

### 7.9 Fewer operations

SW-2492's targets 2 to 4 (one-character dispatch for `oneOf`, `pick`'s notes, character lists
made once) remain the cheapest wins and are independent of everything here; they are already
filed or with Matt.

## 8. Decisions for Matt

- **Reopen operations in place, for native code?** D3430 stopped it after stage B on SW-2417's
  1.3× ceiling. This note measures that the floor of an operation is the effect machinery itself
  (5.7 K for an operation that does nothing, 342 when run in place) and estimates 1.7-3.2× on
  these programs. Changes effect and step counts, not results. *Recommendation:* yes, as a native
  spike on `Tick` first (go/no-go: under 1.5 K an operation), then stage D proper.
- **A design note for compiled handler dispatch (7.2)?** A lowering change with no user-visible
  effect, 9-14% here and something for every effectful program. *Recommendation:* yes, Opus,
  paper; it is also 7.1's prerequisite for a cheap residual.

The rest (7.3 to 7.6) are runtime- or compiler-internal and change nothing a user sees; 7.3 is
already filed (SW-2464), 7.4 to 7.6 aren't.

## 9. Reproducing

The scratch program (`Ops.sw`) and the measuring script are in the lane's scratchpad, not
committed. The shapes that matter:

```
def markLoop (n: Nat) (acc: Nat): {Parse} Nat :=
  match n with
    | Zero => acc
    | Succ m =>
      let x := Parse.mark()
      markLoop m (acc + 1)

def nest (wrap: Text) (depth: Nat) (p: () → {Parse} Nat): {Parse} Nat :=
  match depth with
    | Zero => p()
    | Succ d => Parse.optional (() => nest wrap d p) |> .getOrElse 0   -- or attempt, label, …

-- Tick: one operation, a one-clause Nat state handler
def runTick (p: () → {Tick} a): a :=
  let go: Nat → a :=
    handle p() with
      | return v => s => v
      | Tick.tick u, k => s => k s (s + 1)
  go 0

-- main: Parse.run (List.replicate n 'a') (() => nest wrap depth (() => body mode n))
```

```
nix develop -c cargo build --release -p stitchwort-cli -p stitchwort-standalone --features stitchwort-cli/dev
CARGO_TARGET_DIR=target/profiling nix develop -c cargo build --release -p stitchwort-standalone --features call-counts
stitchwort build --native Ops.sw -o ops
/usr/bin/time -l ./ops mark optional 2 0         # and N = 300000: (I(N) - I(0)) / N
STITCHWORT_RUNTIME=target/profiling/release/libstitchwort_standalone.a \
  stitchwort build --native --count-bodies Ops.sw -o ops-counts
STITCHWORT_CALL_COUNTS=1 ./ops-counts opt none 0 100000 > /dev/null
nix shell nixpkgs#samply -c samply record --rate 8000 --save-only --unstable-presymbolicate -o tick0.json.gz ./ops tick x 0 5000000
python3 -I dev/profile_top.py tick0.json.gz --top 70 --focus rt_loop --focus apply4
stitchwort build --native --pc-map Ops.sw -o opsmap   # bytecode per body in opsmap.pcmap.json
cd aoc && stitchwort build --native Aoc.Year2020.Day18.main -o expr   # and its --count-bodies build
```

Inputs: the day's file joined by `\n` 18 times (expressions) and 20 times (scan) for the counts,
180 and 200 times for the full-size totals. Each scratch run is under 10 s; the profiles under
30 s each; the full-size runs 20 s each.

## 10. Uncertainties, and what I didn't do

- **Shares are time, not instructions.** §3.1's split and every "from shares" figure assume one
  instructions-per-cycle across functions; the allocator's fast path runs at a higher rate than
  generated code (SW-2363), so allocation's instruction share is probably understated and the apply
  path's overstated. The per-kind and per-level costs of §2 are measured and don't depend on this.
- **The options are estimates.** None was built. 7.1's range is the widest: the native half of
  stage D isn't designed, and the residual per operation depends on 7.2. 7.3's step cost is from a
  share; 7.4's closure count is a static upper bound scaled down.
- **The model leaves 16% of expressions and 8% of scan unexplained**, which I attribute to the
  parsers' own code without a breakdown. `stop`'s 3.0 K is a residual of one experiment.
- **Forwards per operation are averages**: the counters don't give a histogram of forwards per
  operation, so §2.2's depths come from the grammars.
- **`mark`'s forward (2.07 K) is dearer than the other operations' (1.43 K);** not chased.
- **Not done:** any change; a value census of the scratch loops; the JS runtime; the other parsing
  benchmarks (bridge, disk, matcher), where the same costs apply in different proportions.

**Findings worth tickets:**

1. Capture-free lambdas built as constants (7.4): small compiler change, about 3% here and some
   on every program.
2. `Parse.labelWhole` nested d deep turns each reading operation into 2^d − 1 operations at
   `runFrom` (`next` under two: 51.8 K against 8.9 K), because each level's clause performs a
   `mark` through the levels outside it (`Parse.further`). Rare today; a level could carry the
   furthest point in its own state from the reading operation's result instead.
3. `sw_resume_begin` copies a unique resumption's fields (7.5).
4. A jump without a `Jumped` object (7.6).
5. R4's estimate (SW-2464) is probably low by about 2×; worth its measured go/no-go.
