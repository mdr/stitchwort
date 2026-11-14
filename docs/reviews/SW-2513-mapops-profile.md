# mapops, profiled natively (SW-2513)

SW-2513, 9 Nov 2026, Sonnet, `lane/SW-2513` from `main` at `6d42da7ce`. Measurement and write-up
only: no compiler, runtime or std code changed. The program is `bench/compare/mapops`: 1 M steps
on std's `Map Nat Nat` (4/10 insert, 3/10 lookup, 2/10 `insertWith`, 1/10 remove, keys below
200,000, the map settling near 166,000 entries). The comparison (SW-2503) has native at 2.38 s and
24.2 G instructions against Lean's `Std.TreeMap` at 0.31 s, about 7.7x, the widest gap in the wide
set.

**How to read the numbers.** Unit: instructions retired (`/usr/bin/time -l`); shares inside one
profile are samply time, so converting a share to instructions assumes an even rate (it is only
roughly so). Everything is **measured** unless marked *estimated*. One run each; instruction counts
repeat to 0.1% or better (SW-2463). The machine was loaded (load average about 20) while this ran,
which does not move instruction counts; the wall times quoted are for comparing runs made together
only. Natives were built by `task profile:native` / `stitchwort build --native` from
`target/bench` (no kache).

## 0. Summary

1. **Half of the program's instructions are a sharing problem, not a Map problem.** `Workload.step`
   does `{ w | map = w.map.insert key value, seed = draw }`. `w.map` is read by a field projection
   while `w` is still alive (the update needs `w`'s other fields), so the map's root has reference
   count 2 for the whole insert. Every unpack down the path then finds a shared node, copies its
   fields (incrementing their counts, which makes the children shared too), and every rebuilt node
   is a fresh allocation while the old one is freed later. The same program with the map passed
   as its own loop argument, or with the record taken apart by a `match` first, gives the same
   answer in **12.62 G instructions instead of 24.24 G (-48%)**: cells allocated 12.95 M to 1.70 M
   (-87%), allocator share 22.8% to 6%, runtime-side drops 18% to about 7%.
2. **After that, the cost is the balance code, in the shape SW-2371 predicted.** `insertWith`
   unpacks the node, calls `balance`, which calls `shape` (a record of sizes, several `Nat`
   multiplications) and `rebuild` (a second dispatch, then `bin` re-adding the sizes); the
   unpacked cell can never be reused because the unpack and the new `Bin` are in different bodies.
   `shape` + `rebuild` are 11.3 M entries each, 24.8% of the instructions of the fixed program.
   Scratch application code that checks the sizes inline and builds the `Bin` in the same body as
   the unpack (std's `Map.Tree.balance` only for the rare rotations) takes the fixed program
   from 12.62 G to **9.39 G (-25.6% more, -61% from the original)**, same answer.
3. **Not the cost, measured:** the `Quot` wrapper, the `Ord` dictionary and generic apply. There is
   no `Map.insert`/`Quot.lift` body in the compiled-body counts at all; the `Nat` comparison is
   `Test EqNat`/`Test Leq` instructions inside `insertWith`'s own body (the optimiser's
   specialisation of `Map.Tree.insertWith` for `Nat.instOrd`); the whole run makes 2
   `sw_apply_*` calls and 7 effect steps (the effect machinery in SW-2511 and the static closures
   of SW-2502 touch nothing here).
4. **Lookup is heavy for what it is**: 4.3 K instructions for a lookup (about 250 per tree level,
   against a handful in Lean), because `get`'s unpacks clone the node's fields (`inc` 64-80% of
   the two unpack instructions) and drop them again; it only reads.
5. **Per-step overhead outside the map is 1.17 K instructions** (generator, `Op.ofDraw`, the
   loop, the record): 9% of the fixed program, 1.17 G (a lookup on an empty map; includes one
   empty `get`).
6. **Lean does the whole run in 1.83 G instructions** (measured: `bench/compare/lean`'s `mapops`,
   1.83 K per step): 13.2x fewer than the original, 6.9x fewer than the fixed program, 5.1x
   fewer than the fixed-and-fused one.

Ranked targets (details in section 4):

| # | Target | Instructions (G) | Basis |
|---|---|---:|---|
| 1 | Record update keeps the old record alive: take the replaced field out of a unique record (compiler), or write the program with the map passed apart | 24.24 -> 12.62 (**-48%**) | measured (program change; compiler fix *estimated* to give the same where `w` is unique) |
| 2 | Balance and the node it replaces in one body: inlining `balance`/`rebuild`/`bin` into `insertWith`/`remove`, or a fused `balanceL`/`balanceR` (SW-814 again) | 12.62 -> 9.39 (**-25.6%**) | measured with hand-written application code (upper bound of what inlining gives) |
| 3 | Read-only walks (`get`, `contains`, the compare-only descent) not copying fields: borrowed parameter, or `Field` projections instead of a cloning `Unpack` | about -0.5 to -0.7 G of 12.62 (-4 to -5%) | *estimated* from the `inc`/`dec` shares of `get` (44% of its 12.2%) |
| 4 | `remove`/`glue`/`deleteMin`/`minKey`/`minValue` the same way as 2 (`remove` is 20% of the fixed program inclusive) | *not measured* (remove is 1/10 of the steps) | n/a |
| 5 | SW-1825, native `Map.Tree.get`/`insertWith` for structural orders | ceiling: Lean's 1.83 G | *estimated*; overlaps 2, 3 and 4 completely for `Nat` keys |
| 6 | Loop overhead: `Nat` arithmetic in the generator and `Op.ofDraw` | up to -1.17 G | measured upper bound; not a Map matter |

## 1. Instructions per operation, by kind

Method: `kinds.sw`/`loop.sw`, scratch copies of `main.sw` taking `pre steps mode` arguments:
`pre` mixed steps (the real mix, 1 M of them: the map reaches its steady 166 K) and then `steps`
steps of one kind (modes 0 insert, 4 lookup, 7 update, 9 remove; 99 the mix). Cost per step =
(total - the `pre` run) / steps; it includes the 1.2-1.4 K per-step overhead. Original program
(record update) and the fixed one (map as its own argument; `loop.sw`):

| Kind | Original (instr/step) | Fixed (`loop.sw`) | Fixed and fused insert (`fused.sw`) |
|---|---:|---:|---:|
| insert (growing 166 K -> 200 K) | 34.9 K | 13.6 K | 8.1 K |
| `insertWith` update | 35.0 K | 13.6 K | 8.1 K |
| lookup | 4.7 K | 4.3 K | 4.3 K |
| remove (run alone: the map shrinks to 1,105, so shallower than the mix) | 18.8 K | 17.1 K | 17.1 K (std's) |
| whole run, the real mix | 24.24 G | 12.62 G | 9.39 G |
| per-step overhead (empty map, lookups) | 1.41 K | 1.17 K | n/a |

An insert on a 170-200 K map visits about 14.3 `insertWith` levels (10.0 M entries over 700 K
inserts and updates, section 2), so the original spends **about 2.4 K instructions a level** and
the fixed program **about 950**. A lookup visits about 16.7 levels (5.0 M `get` entries over
300 K lookups): **250 a level**. Lean's whole run is 1.83 K a step on average.

Caveat on the remove row: the 4+3+2 steps' sums leave a residual for the tenth step of 18.7 K in
the original (agrees with the 18.8 K measured) but 32 K in the fixed and fused runs (against 17 K
measured alone). I did not find out why: remove on a shrinking map is not steady state, and
insert-only growth from 166 K to 200 K is not either. The kinds table is therefore good to the
order of 10-20% per row; the three whole-run totals are exact.

## 2. Where the instructions go

### 2.1 The original (record update): `task profile:native -- mapops --by-instruction --bodies 12`

Self time by kind (2,337 samples): generated code 52.9%, allocator (mimalloc) 22.8%, runtime in
Rust 15.2% (of which `value::free` 6.9%, `drop_glue<Value>` 4.5%, `Fields::drop` 3.0%,
`Rc<[Value]>::drop_slow` 2.6%), kernel/libc 6.7%, runtime entry points 1.9%. So **41% of the time
is allocating and freeing** cells, in a program whose trees could be updated in place.

Compiled bodies by entries (counting build):

| Body | Entries | Self time share |
|---|---:|---:|
| `Map.Tree.rebuild` | 11.28 M | 6.3% |
| `Map.Tree.shape` | 11.28 M | 6.6% |
| `insertWith.%match1[0][1]` (`Less`/`Greater` arms) | 6.66 M | 16.1% |
| `insertWith.%match1[3]` (the recursion's other half) | 3.34 M | 7.7% |
| `Map.Tree.get.%match1` | 5.00 M | 8.1% |
| `Map.Tree.remove.%match1[4]` | 1.66 M | 3.4% |
| `Workload.step`, `.run`, `Op.ofDraw` and their matches | 1.0 M each | about 4% |
| `glue`, `deleteMin`, `minKey`, `minValue`, rotations | under 0.4 M each | under 1% each |

Runtime calls from native code: `sw_cell_new` **12,949,295** (about 13 per step, 18 per
insert/update/remove), `sw_drop_words` 1,000,006, `sw_drop_reuse` 49,430; everything else under
10 calls. 186,380 of the cells came from the cell cache. In `insertWith.%match1[0][1]` the two
`Unpack`s are 20% of the body (`inc` 89%, 65%) and the two `balance` calls 20%: fields copied
because the node is shared.

### 2.2 After the sharing is removed (`loop.sw`, same tool, program `mapopsloop` temporarily
registered, not committed)

Self time by kind (4,382 samples): generated code **87.6%**, allocator 6.0%, Rust runtime 4.8%.
`sw_cell_new` **1,698,107** (-87%); 12.62 G instructions, 1.26 s user (the original: 2.18 s).
Bodies (self share and instructions at 12.62 G):

| Body | Entries | Self | Instructions | Per entry |
|---|---:|---:|---:|---:|
| `insertWith.%match1[0][1]` + `[3]` | 10.0 M | 35.9% | 4.5 G | 450 |
| `Map.Tree.shape` | 11.28 M | 13.7% | 1.7 G | 153 |
| `Map.Tree.rebuild` | 11.28 M | 11.1% | 1.4 G | 124 |
| `Map.Tree.get.%match1` | 5.0 M | 12.2% | 1.5 G | 308 |
| `Map.Tree.remove.%match1[4]` | 1.66 M | 6.9% | 0.9 G | 520 |
| `Workload.loop`, matches, `Op.ofDraw` | 1.0 M | about 6% | 0.75 G | 750 |

Within `insertWith`'s bodies, the two `Unpack`s are 34-37% (they now move the fields out, `work`
100%, no `inc`), the `balance` calls 10-11%, the `Const`/`Test` pairs that stand for the `Nat`
comparison 8-10%. In `shape` 63% is "untagged" (code outside the instruction map: the `Nat`
arithmetic and the Shape allocation-free constant returns), `Field` reads of the sizes 8%. In
`rebuild` the `CtorReuse` is 18.5% of the body, and `Return`/drops of the `Shape` and subtrees
another 20%. In `get`, the two `Unpack`s are 46% and `inc` is 33% of the body: the walk still
clones, because the map is alive during a lookup.

### 2.3 The suspects in the brief

- **Comparison through the `Ord` dictionary:** none at run time. `Test { op: Nat(EqNat) }` and
  `Test { op: Nat(Leq) }` inside `insertWith`/`get` are the comparison; 2.5-4.5% of those
  bodies (about 1% of the profile).
- **The `Quot` wrapper:** no body, no call, no cell. `Map.insert` is `{ raw = Quot.mk (…) }`
  around the tree, erased at run time ("a map is its tree, in one record", `Map.sw`).
- **Balance:** 13.7% + 11.1% of the fixed program directly, plus the `balance` call sequences
  in the `insertWith` bodies (10-11% of them); about 30% of the fixed program in all.
- **Allocation and freeing:** 41% of the original (all of it avoidable by target 1), 11% of the
  fixed program.
- **Generic apply / closures / effects:** nothing: 2 `sw_apply_cached`, 2 `sw_pap`, 7 effect
  steps, once each at start-up.

## 3. How Lean's `Std.TreeMap` does the same work

Source read: `Std/Data/DTreeMap/Internal/{Def,Balancing,Operations}.lean` in the toolchain
(`lean4-4.34.1`). Measured: 1.83 G instructions, 0.28 s user, 12.9 MB.

- **The same algorithm.** `Impl` is `inner (size : Nat) k v l r | leaf` with the same constants
  (`delta := 3`, `ratio := 2`), a weight-balanced tree like Stitchwort's `Map.Tree`, so trees
  have the same depth. The difference is how a level is run.
- **Balance is fused and inlined.** `insert!` is `match compare k k' with | .lt => balanceL! k' v'
  (insert! k v l) r | …`. `balanceL!` is `@[inline]` and does one `match` on both children,
  building the result node directly with `1 + ls + rs` (no separate shape value, no second
  dispatch, no `bin` pass). The unpack of the old node and the construction of the new one are in
  one function, so Lean's reset/reuse reuses the old cell in place when the tree is unique,
  which here it always is (`{ w with map := w.map.insert … }` compiles to a consuming update).
- **The comparison is `compare` on `Nat`, specialised** to machine-word comparison for small
  naturals; the `Ord` instance is resolved at compile time.
- **Reads borrow.** `get?`/`getD` take the tree as a borrowed parameter (Lean's inferred borrow
  annotations), so a lookup does no reference-count traffic.
- **Update is `getD` then `insert`** in Lean's `mapops` (two descents), not a fused
  `insertWith`; it still wins.
- **Proofs are erased**, as ours are.

So the Lean/ours difference is, in order: unique update with cell reuse (our target 1 is just
having it at all), a fused inlined balance (target 2), borrowed reads (target 3), and then
instruction-level costs of a bytecode-derived calling convention (our `Unpack` with its token
and `check`/`prologue` parts) that are not Map-specific.

## 4. Targets, ranked

**1. The record update (measured -48%; compiler fix recommended).** Variants, all giving
`166073 25450745`:

| Variant | Instructions (G) | User s |
|---|---:|---:|
| original (`{ w \| map = w.map.insert … }`) | 24.24 | 2.18 |
| `Workload.loop map seed check from steps mode` (state as arguments) | 12.62 | 1.25 |
| `match w with \| { map = map, seed = seed, check = check } => …` then rebuild the record | 12.62 | 1.21 |

The second and third give the same count, so the cheap source-level fix is to take the record
apart before the update, which the AoC programs and the roguelike can adopt now. The compiler fix:
a record update `{ w | f = e, … }` whose `w` is unique and not used after should move the
untouched fields out and drop the replaced one, and `w.f` inside `e` should then be a move, not
a clone. How many AoC days and tests write this pattern is a grep (not done); SW-2371 found the
same effect in `Graph.searchFrom` (-17% in that program) from a parameter held twice, so this is a
class, not one program. *Estimated* effect elsewhere: the share of Map work in the program
times the up-to-48%.
Overlap: SW-814's measured -0.17% was taken where the maps were shared this way; **that
number is not evidence against a fused balance** (target 2).

**2. Inlined or fused balance (measured -25.6% on top of 1, -61% in all).** Scratch
`fused.sw`: `Map.Tree.insertWith`'s two recursive arms check
`ds + rs < 2 ∨ ds <= rs * 3` (one side only grew) and build `Bin (Succ (ds + rs)) d kk vv r` in
the same body as the unpack; otherwise they call std's `Map.Tree.balance`. Per insert 13.6 K ->
8.1 K (-40%). Two ways to get it into std:
(a) fused `balanceL`/`balanceR` as SW-814 tried (8 new definitions and lemmas; the proof burden
was what made SW-814 drop it at -0.17%); (b) a compiler inlining pass for small non-recursive
definitions (`balance`, `rebuild`, `bin`, `shape`), so the unpack token reaches the `Bin`: no std
or proof change. (b) is SW-2371's cause 2 and probably the better fix, since it helps
every function that rebuilds a node it unpacked. *Estimated* that (b) gets most of (a)'s
25.6%; the scratch is the upper bound (it skips `shape`'s `Shape` value too). The scratch's
balance condition is the standard one-sided test, not proven, and its shape could differ from
std's on unbalanced input (not checked beyond the same final answer).

**3. Borrowed reads (estimated -4 to -5% of the fixed program).** `get` is 12.2% of the fixed
program and 44% of that is `inc`/`dec` copies of fields a read-only walk never needs. With the
two unpacks as `Field` reads of the key and the child, a level should cost about 100 instead of
308. That would be -0.5 to -0.7 G (*estimated*: assumes the `inc`/`dec` share is removed and the
rest stays). Benefits every `contains`, `get`, `getOr`, `Set.contains` and fold.

**4. `remove`** and the pieces it calls (`glue`, `deleteMin`, `minKey`, `minValue`) are 20% of
the fixed program inclusive (1.66 M entries; 0.9 G self in `remove`), on a tenth of the
steps; they pass through `balance` too, so 2 should carry over. Not measured separately. A
`minView`-based `glue` (one walk instead of `minKey`, `minValue`, `deleteMin`: three) would be
a further small saving: 57,641 `glue` calls cost three walks each.

**5. SW-1825 (native `Map.Tree` functions).** Natives would remove the interpreter cost of
targets 2 to 4 for structural key orders in one stroke; Lean's 1.83 G is the ceiling
(*estimated*: a native `insertWith` in Rust at the same depth and 16 bytes of node should be
close to Lean's per-level cost). It is the larger change (a second implementation to keep equal to
the Stitchwort definition) and it does not help Map users with a custom `Ord`; targets 1 to 3 do.
The measurements say: do target 1 first (it makes SW-1825's baseline honest), and re-decide
SW-1825 after 2 and 3 land. Overlap with SW-2511 and SW-2502: none for this program.

**6. The loop itself**, 1.17 K a step (9% of the fixed program): `seed * 48271 % modulus`,
`draw / keys % 10`, `draw % keys`, `step % 1000`, the matches. Not a Map matter; it shows what
`Nat` arithmetic and a four-way `match` cost in compiled code (about a thousand instructions for
about eight operations). Worth a separate look with a loop-only variant (not done).

## 5. Commands

All from the worktree `.claude/worktrees/SW-2513`; variants in the session's scratchpad
(`scratchpad/mo/`: `kinds.sw`, `loop.sw`, `destr.sw`, `fused.sw`, `m.sh`/`m2.sh`).

```
nix develop -c task profile:native -- mapops --by-instruction --bodies 12 --top 30
   # 12 s of build (kache-less cargo), recording and counting build about 2 min in all
/usr/bin/time -l ./kinds PRE STEPS MODE        # "instructions retired"
stitchwort build --native kinds.sw -o kinds    # target/bench/release/stitchwort
nix develop .#compare -c bash -c 'lake build mapops; /usr/bin/time -l .lake/build/bin/mapops'
   # in bench/compare/lean: 1,832,297,117 instructions
```

Results: `task profile:native -- mapops`: 24.24 G (profile) and 24,236,121,459 (`kinds 1000000 0 0`);
`loop`: 12,624,844,666; `destr`: 12,617,631,000; `fused`: 9,386,782,912; Lean 1,832,297,117.
The `loop` variant was profiled by temporarily adding `bench/compare/mapopsloop` and a
`programs.toml` entry (reverted). The scratch `loop.sw` differs from `main.sw` only in
`Workload.loop` replacing `step`/`run`; `fused.sw` additionally uses `Map.Tree` directly with its
own `Fused.go` for insert and `insertWith`, std's `get`, `remove` and `foldLeft`.

## 6. What I didn't do, and what I'm unsure of

- **Not done:** the value census (`value-census` build, SW-2425): the cell counts above are
  `sw_cell_new` calls, which are what the effect-free program allocates; object sizes and a
  census by constructor would add little. A fused `remove`, a `get` with `Field` reads, a
  compiler change of any kind (all would be estimates turned into measurements). A grep of how
  many AoC programs use the record-update pattern of target 1. The `finish` fold (about 332 K
  `foldLeft` entries, under 1%).
- **Uncertain:** (1) the mapping from samply share to instructions in section 2.2 is
  rough, and the instruction-by-instruction splits are of the instruction map's categories
  ("untagged" is code the map doesn't attribute). (2) The remove row of section 1 (see the
  caveat there). (3) That a compiler fix for target 1 gives the full 48%: the scratch took the
  fields apart at the source level; the lowering of `{ w | … }` and of the field read were not
  read. (4) That `w.map` is the thing held twice: inferred from the two source variants
  that fix it and from the shared-unpack signature (`inc` 89%), not from a per-unpack unique/shared
  count (SW-2371's instrumentation was not rebuilt). (5) The fused scratch is not the
  proof-carrying std change; its tree shape was not compared with std's beyond the identical
  answer. (6) Lean's per-kind costs were not measured (only the whole run), and the Lean
  program does `getD` + `insert` where ours does `insertWith`.
