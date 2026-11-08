# SW-2422: allocation and freeing in native code, split by cause

Lane SW-2422, Sonnet, 8 Nov 2026. A measurement; no product code changed. It splits the 50% of
native time that [SW-2417](SW-2417-native-effect-share.md) found in allocating, freeing and cloning
into causes, joins the shares to the counts of [SW-2425](SW-2425-value-census.md)'s census, and ranks
the cheapest cuts. Shares are of all samples on one thread; Speedwell was also running a fuzzer, so
no times. **[measured]** = read from a profile or counter; **[estimated]** = derived, with the rule given.

## The reading

1. **Freeing costs about 2.5 times what making does.** On expressions and scan, 14% / 12% of
   time is `mi_malloc` and its Rust front end, and 35% / 36% is the free side (the walk 27%,
   `mi_free` 8-9%); clones add 2%. The cheap cuts are about freeing fewer, or cheaper, objects.
2. **Closures are the biggest single cause**: 8-10% of time on expressions, scan, matcher, 12.6% on
   octopus, 6% on dijkstra (making plus freeing, the freeing share **[estimated]** by object count).
   A closure is two allocations (`Rc<Fun>` and the captures `Box<[Value]>`, `sw_closure`). The effect
   objects come next (8.7% on expressions and scan), then the cells the *runtime* builds
   (190 M of expressions' 322 M cells, 59%; 175 M of scan's 293 M).
3. **The free walk is per-object overhead, not depth.** Of the time in freeing cells and
   closures, 45-50% is on root objects whose free finds nothing to walk below (a scalar-only cell, a
   closure whose captures are shared or scalar); children reached by the walk are 15-20%. The census says why on
   octopus: 92% of cell fields are scalars. Cells freed whose fields are scalars cost about what
   pointer-holding ones do.
4. **About a quarter of the free time cannot be attributed from the stack** (8-9% of all time on
   expressions, scan, octopus): `mi_free` and drop glue called straight from `value::free`'s loop or
   `drop_glue<Value>`, with no typed frame above.
5. **`binary-trees` shows only 7.9%**, all in `sw_cell_new`; its frees probably go through the cell
   cache and generated code, which this view does not see.

## Method

- `nix develop -c task profile:native -- expressions scan matcher dijkstra octopus binary-trees --top 5 --no-counts`
  (samply, as [SW-2296](SW-2296-native-profiles.md)), then `dev/profile_causes.py`, a new helper
  built on `profile_top.py`'s loader (`python3 dev/profile_causes.py target/profile/NAME.json.gz 16 [shape]`).
  Expressions was profiled twice (a first run and the counting run's, 41.8 k and 34.1 k samples): 51.7%
  and 51.1% in memory work, so the shares are steady to about a point.
- A sample is **memory work** if any frame is mimalloc, Rust's allocator front end, drop glue,
  `value::free`, `Fields::drop`, `take_children`, an `Rc` `drop_slow`, `RawVec` growth or
  `Value::clone` (memmove is left out). Total 51.1% on expressions, against SW-2417's 52%.
- Each such sample is classified three ways. **Operation** by its leaf frame: malloc side
  (`mi_malloc`, `__rust_alloc`, `RawVec::finish_grow`, `into_boxed_slice`...), `mi_free`, the
  **walk** (`drop_glue<Value>`, `value::free`, `Fields::drop`, `take_children`, `drop_slow`),
  or clone. **Making site**, for the malloc side: the first frame above the allocator that is not
  allocator glue (`sw_closure`, `sw_pap`, `sw_cell_new`, `Value::data::<N>` and its caller, `sw_bind`,
  `sw_eff_*`, `sw_apply_prepare`, a take_children `Vec` growth = the drop worklist). **Freed object**, for
  the free side: the innermost typed drop frame on the stack (`Rc<Fun>::drop_slow`,
  `Fun::take_children` = a `Fun`; `Fields::drop` or `Rc<[Value]>::drop_slow` = a cell;
  `Resume`, `Handler`). **Trigger** is the frame just outside the outermost memory frame.
- Counts: census (`cargo build --release -p stitchwort-cli --features stitchwort-rt/value-census
  --target-dir target/census`, run with `STITCHWORT_VALUE_CENSUS=out.txt stitchwort run`, on the
  bytecode machine, which allocates object for object as native code does) and native
  `call-counts` (`task profile:native` without `--no-counts`). Where both exist they agree:
  `sw_closure` 106,429,698 against census closures 106.43 M on expressions; `sw_cell_new` 20,606,307
  against 20.7 M cells on octopus.
- The inputs are the comparison sizes of `bench/compare/programs.toml`.

## Per program

Each table: the time of one cause, split into making (the malloc side) and freeing (walk and
`mi_free`), and how many objects the run makes. Rows 1-6 divide the measured `Fun` and cell free
time by each kind's share of the objects the census counted **[estimated]**: the stack names
the freed object's type only as `Fun` or cell, not which kind. "Cells made by the runtime" is the
census's cell total minus `sw_cell_new` minus `sw_bind`: the effect machinery (`skipped`'s `Call`,
`done_k`, `forwarded`, pairs) and primitives. The Bind row is part of the cell total in the census and
shown apart. Rows add to the memory-work total less the "other sites" line.


### expressions

Allocation, freeing and cloning: **51.1%** of 34141 samples (alloc 14.0%, free walk+drop 35.1%, mi_free 7.9%, clone 2.0%).

| Cause | Making (malloc side) | Freeing (walk + `mi_free`) | Total | Allocations (count) |
|---|---:|---:|---:|---:|
| closures (`sw_closure`: `Rc<Fun>` + captures `Box`) | 2.8% | 6.6% | 9.5% | 106.4M |
| paps (`sw_pap`) | 0.4% | 1.8% | 2.2% | 29.5M |
| cells made by generated code (`sw_cell_new`) | 1.8% | 2.9% | 4.7% | 85.6M |
| cells made by the runtime (effect machinery, prims) | 2.2% | 6.4% | 8.6% | 190.1M |
| Bind nodes (`sw_bind`, 2-field cells) | 0.7% | 1.6% | 2.3% | 46.6M |
| Resume, Handler, StateRun, StateK, Jumped (effect objects) | 1.4% | 7.3% | 8.7% | 117.4M |
| drop worklist `Vec` (in `Fun`/`Fields`/`Delay` drop) | 3.3% | - | 3.3% | - |
| apply (`sw_apply_prepare`: argument vector etc.) | 1.0% | - | 1.0% | - |
| arrays, texts, big numbers (prims) | 0.2% | - | 0.2% | 0 arrays, 2.1M texts, 0 big |
| clones (`Value::clone`) | - | 2.0% | 2.0% | - |
| freeing not attributable (`mi_free`/walk called straight from drop glue or `value::free`) | - | 8.5% | 8.5% | - |

Making, other sites: 0.1%.  Free+walk rows 1-6 split the `Fun`/`cell` totals by object counts (**estimated**); the unattributed row is measured.

### scan

Allocation, freeing and cloning: **49.6%** of 23137 samples (alloc 11.8%, free walk+drop 35.6%, mi_free 8.9%, clone 2.2%).

| Cause | Making (malloc side) | Freeing (walk + `mi_free`) | Total | Allocations (count) |
|---|---:|---:|---:|---:|
| closures (`sw_closure`: `Rc<Fun>` + captures `Box`) | 2.3% | 5.8% | 8.1% | 92.0M |
| paps (`sw_pap`) | 0.2% | 1.9% | 2.1% | 30.6M |
| cells made by generated code (`sw_cell_new`) | 1.1% | 3.2% | 4.2% | 75.3M |
| cells made by the runtime (effect machinery, prims) | 2.0% | 7.4% | 9.3% | 175.5M |
| Bind nodes (`sw_bind`, 2-field cells) | 0.6% | 1.8% | 2.4% | 43.0M |
| Resume, Handler, StateRun, StateK, Jumped (effect objects) | 1.4% | 7.4% | 8.8% | 117.4M |
| drop worklist `Vec` (in `Fun`/`Fields`/`Delay` drop) | 2.7% | - | 2.7% | - |
| apply (`sw_apply_prepare`: argument vector etc.) | 1.2% | - | 1.2% | - |
| arrays, texts, big numbers (prims) | 0.1% | - | 0.1% | 0 arrays, 0.4M texts, 0 big |
| clones (`Value::clone`) | - | 2.2% | 2.2% | - |
| freeing not attributable (`mi_free`/walk called straight from drop glue or `value::free`) | - | 8.2% | 8.2% | - |

Making, other sites: 0.1%.  Free+walk rows 1-6 split the `Fun`/`cell` totals by object counts (**estimated**); the unattributed row is measured.

### matcher

Allocation, freeing and cloning: **30.5%** of 5185 samples (alloc 8.1%, free walk+drop 21.0%, mi_free 6.4%, clone 1.3%).

| Cause | Making (malloc side) | Freeing (walk + `mi_free`) | Total | Allocations (count) |
|---|---:|---:|---:|---:|
| closures (`sw_closure`: `Rc<Fun>` + captures `Box`) | 2.5% | 7.3% | 9.7% | 18.5M |
| paps (`sw_pap`) | 0.1% | 0.7% | 0.7% | 1.7M |
| cells made by generated code (`sw_cell_new`) | 1.2% | 1.7% | 2.9% | 16.9M |
| cells made by the runtime (effect machinery, prims) | 0.6% | 2.4% | 3.0% | 24.0M |
| Bind nodes (`sw_bind`, 2-field cells) | 0.2% | 0.2% | 0.4% | 2.0M |
| Resume, Handler, StateRun, StateK, Jumped (effect objects) | 0.5% | 2.4% | 2.9% | 6.2M |
| drop worklist `Vec` (in `Fun`/`Fields`/`Delay` drop) | 2.8% | - | 2.8% | - |
| apply (`sw_apply_prepare`: argument vector etc.) | 0.3% | - | 0.3% | - |
| arrays, texts, big numbers (prims) | 0.0% | - | 0.0% | 0 arrays, 2k texts, 0 big |
| clones (`Value::clone`) | - | 1.3% | 1.3% | - |
| freeing not attributable (`mi_free`/walk called straight from drop glue or `value::free`) | - | 6.3% | 6.3% | - |

Making, other sites: 0.0%.  Free+walk rows 1-6 split the `Fun`/`cell` totals by object counts (**estimated**); the unattributed row is measured.

### dijkstra

Allocation, freeing and cloning: **31.6%** of 1512 samples (alloc 8.1%, free walk+drop 22.5%, mi_free 5.2%, clone 1.1%).

| Cause | Making (malloc side) | Freeing (walk + `mi_free`) | Total | Allocations (count) |
|---|---:|---:|---:|---:|
| closures (`sw_closure`: `Rc<Fun>` + captures `Box`) | 1.7% | 4.3% | 5.9% | 3.1M |
| paps (`sw_pap`) | 0.7% | 1.9% | 2.6% | 1.4M |
| cells made by generated code (`sw_cell_new`) | 3.9% | 7.4% | 11.4% | 8.9M |
| cells made by the runtime (effect machinery, prims) | 0.3% | 3.5% | 3.7% | 4.1M |
| Bind nodes (`sw_bind`, 2-field cells) | 0.0% | 0.1% | 0.1% | 82k |
| Resume, Handler, StateRun, StateK, Jumped (effect objects) | 0.0% | 0.2% | 0.2% | 0.1M |
| drop worklist `Vec` (in `Fun`/`Fields`/`Delay` drop) | 1.4% | - | 1.4% | - |
| apply (`sw_apply_prepare`: argument vector etc.) | 0.0% | - | 0.0% | - |
| arrays, texts, big numbers (prims) | 0.0% | - | 0.0% | 209 arrays, 105 texts, 0 big |
| clones (`Value::clone`) | - | 1.1% | 1.1% | - |
| freeing not attributable (`mi_free`/walk called straight from drop glue or `value::free`) | - | 5.2% | 5.2% | - |

Making, other sites: 0.1%.  Free+walk rows 1-6 split the `Fun`/`cell` totals by object counts (**estimated**); the unattributed row is measured.

### octopus

Allocation, freeing and cloning: **39.6%** of 2371 samples (alloc 9.1%, free walk+drop 29.6%, mi_free 8.5%, clone 1.0%).

| Cause | Making (malloc side) | Freeing (walk + `mi_free`) | Total | Allocations (count) |
|---|---:|---:|---:|---:|
| closures (`sw_closure`: `Rc<Fun>` + captures `Box`) | 2.2% | 10.4% | 12.6% | 7.0M |
| paps (`sw_pap`) | 0.0% | 0.0% | 0.0% | 3k |
| cells made by generated code (`sw_cell_new`) | 4.4% | 10.7% | 15.1% | 20.6M |
| cells made by the runtime (effect machinery, prims) | 0.0% | 0.0% | 0.0% | 89k |
| Bind nodes (`sw_bind`, 2-field cells) | 0.0% | 0.0% | 0.0% | 4k |
| Resume, Handler, StateRun, StateK, Jumped (effect objects) | 0.0% | 0.0% | 0.0% | 6k |
| drop worklist `Vec` (in `Fun`/`Fields`/`Delay` drop) | 2.1% | - | 2.1% | - |
| apply (`sw_apply_prepare`: argument vector etc.) | 0.0% | - | 0.0% | - |
| arrays, texts, big numbers (prims) | 0.3% | - | 0.3% | 91k arrays, 28 texts, 0 big |
| clones (`Value::clone`) | - | 1.0% | 1.0% | - |
| freeing not attributable (`mi_free`/walk called straight from drop glue or `value::free`) | - | 8.4% | 8.4% | - |

Making, other sites: 0.0%.  Free+walk rows 1-6 split the `Fun`/`cell` totals by object counts (**estimated**); the unattributed row is measured.

### binary-trees

Allocation, freeing and cloning: **7.9%** of 1484 samples (alloc 7.0%, free walk+drop 0.9%, mi_free 0.2%, clone 0.0%).

| Cause | Making (malloc side) | Freeing (walk + `mi_free`) | Total | Allocations (count) |
|---|---:|---:|---:|---:|
| closures (`sw_closure`: `Rc<Fun>` + captures `Box`) | 0.0% | 0.2% | 0.2% | 21 |
| paps (`sw_pap`) | 0.0% | 0.0% | 0.0% | 4 |
| cells made by generated code (`sw_cell_new`) | 7.0% | 0.2% | 7.2% | 68.3M |
| cells made by the runtime (effect machinery, prims) | 0.0% | 0.0% | 0.0% | - |
| Bind nodes (`sw_bind`, 2-field cells) | 0.0% | 0.0% | 0.0% | - |
| Resume, Handler, StateRun, StateK, Jumped (effect objects) | 0.0% | 0.3% | 0.3% | 39 |
| drop worklist `Vec` (in `Fun`/`Fields`/`Delay` drop) | 0.0% | - | 0.0% | - |
| apply (`sw_apply_prepare`: argument vector etc.) | 0.0% | - | 0.0% | - |
| arrays, texts, big numbers (prims) | 0.0% | - | 0.0% | 0 arrays, 66 texts, 0 big |
| clones (`Value::clone`) | - | 0.0% | 0.0% | - |
| freeing not attributable (`mi_free`/walk called straight from drop glue or `value::free`) | - | 0.1% | 0.1% | - |

Making, other sites: 0.0%.  Free+walk rows 1-6 split the `Fun`/`cell` totals by object counts (**estimated**); the unattributed row is measured.


## Who triggers it (expressions and scan, **[measured]** inclusive of the memory work beneath)

| Trigger (frame outside all memory work) | expressions | scan |
|---|---:|---:|
| generated code bodies (`sw_drop_words`, drop glue inlined in them) | 14.9% | 18.8% |
| `sw_apply_prepare` (drops the called function value, clones held arguments) | 6.5% | 8.0% |
| `apply1` (`sw_drop_deferred`, dropping after a call) | 5.4% | 4.8% |
| `sw_eff_step` (the effect loop's step) | 7.8% | 3.6% |
| `effect::pair` (taking the two fields of a `Call`/`Bind` cell) | 3.9% | 4.1% |
| `sw_closure` | 2.9% | 2.3% |
| `Value::data::<2>` (two-field cells built in the runtime) | 2.1% | 2.2% |
| `sw_cell_new` | 1.3% | 1.1% |
| `rt_loop`/`rt_resume`, `effect::field`, `skipped`, `sw_resume_begin` | 2.9% | 1.9% |

The effect loop alone (`sw_eff_step`, `pair`, `field`, the loop, `skipped`) triggers about 15% of
expressions' time in memory work and 9% of scan's, mostly by dropping the cells and `Resume`s it takes apart.

## Where the free walk spends

Free + walk time, by the object and by whether it was the root of a free or a child reached by
the walk, and whether it had children **[measured]**, as a share of all time:

| Program | cell, root, no children below | cell, root, children | cell, nested | `Fun` etc., root, no children | `Fun` etc., root, children | `Fun` etc., nested | not attributable |
|---|---:|---:|---:|---:|---:|---:|---:|
| expressions | 5.7% | 2.8% | 2.4% | 6.5% | 6.9% | 2.4% | 9.0% |
| scan | 6.2% | 2.7% | 3.4% | 6.8% | 6.1% | 2.2% | 9.0% |
| matcher | 3.1% | 0.8% | 0.4% | 5.9% | 4.0% | 0.5% | 6.8% |
| dijkstra | 5.1% | 5.3% | 2.0% | 0.7% | 0.7% | 3.5% | 5.8% |
| octopus | 5.9% | 1.8% | 3.0% | 6.5% | 3.9% | 0.1% | 8.4% |

Joined to the census (**[measured]** counts at creation; a free sees the same objects):

| Program | cell fields that are pointers | closure and pap captures that are pointers | cells with one / two fields |
|---|---:|---:|---:|
| expressions | 82% | 82% | 38% / 58% |
| scan | 82% | 87% | 35% / 60% |
| matcher | 61% | 63% | 69% / 30% |
| dijkstra | 42% | 92% | 40% / 52% |
| octopus | 8% | 73% | 1% / 99% |
| binary-trees | 50% | 62% | 0% / 100% |

- **Cells of scalars are not cheap.** Octopus's cells are 92% scalar fields, yet its cell free
  time is 10.7%, 5.9% of it on cells with nothing below: the cost is the strong-count test, the
  `take_from` scan, the empty worklist's call to `value::free`, and `mi_free`, once per cell.
- **Closures are freed with their captures mostly walked.** 82-92% of captures hold a pointer
  (functions and cells); 41-62% of the `Fun` free time (14% on dijkstra) is on roots with nothing the walk
  could free: the walk takes children only of a unique object, so shared or scalar captures end it.
- **Dijkstra differs**: its frees are cells (11%), many of them with children (5.3% root-with-children),
  the list/heap nodes.

## Cuts

Estimates are of the share of *total* time saved on expressions and scan unless a program is named;
each is **[estimated]** from the rows above, and none was built. "Moot" means the cut disappears if
compact values (docs/proposals/compact-values.md) land with option A.

1. **One-slot drop worklist.** Today's `Fields`/`Fun`/`Delay` drop allocates a `Vec` (cap 4 =
   96 B) for the first deep child, and frees it after: the malloc side is 3.3% / 2.7% /
   2.8% / 1.4% / 2.1% (expressions / scan / matcher / dijkstra / octopus), measured, and its free
   is part of the unattributed 8%. Keep the first deep child in a local `Option<Value>` and push
   to a `Vec` only for a second; most roots (a closure with one pointer capture, a list cell, a
   `Bind`) have exactly one. SW-2421 tried a thread-local and a `SmallVec<[Value; 8]>` (both slower,
   +3% and +4% instructions); this keeps 24 bytes on the stack, not 192, and calls no TLS.
   **Saves 1.5-2.5%.** Effort small (an hour; judge by instruction count as SW-2421 did).
   Not moot under C, E or A (the drop structure is the same).
2. **Do not allocate a `Fun` just to flip a resumption's eager/lazy flag.** `Fun::Resume(Rc<Resume>, bool)`
   is an `Rc<Fun>` around an `Rc<Resume>`; `resume_lazily` and `skipped` make a new wrapper each
   time (census, expressions: 30.5 M `Fun::Resume` and 18.7 M `StateK` wrappers for 49.2 M `Resume`s; native
   counts 29.3 M `sw_resume_begin`, 29.1 M forwarding clauses skipped). When the wrapper
   is unique (`Rc::get_mut`), set the flag in place; or keep both wrappers in the `Resume`. The effect-object
   row is 8.7-8.8% on expressions and scan; the wrappers are 42% of its objects. **Saves 2-3%** on
   expressions and scan, nothing on the others (matcher has 2.5 M resumes: about 0.3%). Effort small to
   medium (Sonnet, 1-2 h; `effect.rs`, `native_abi.rs` apply). Not moot.
3. **Make closure and pap captures without the `Vec` machinery and the Rust allocator shim.**
   `sw_closure` and `sw_pap` collect `(0..n).map(read)` into a `Box<[Value]>`
   (`into_boxed_slice` 0.6% self, `finish_grow`), and each allocation goes through
   `__rust_no_alloc_shim_is_unstable_v2` and `__rust_alloc` (0.93% and 0.88% self on expressions, SW-2417's
   item 3, SW-2321). `Box::new_uninit_slice` plus one `copy_nonoverlapping`, and calling mimalloc
   directly. **Saves 0.7-1.2%.** Effort small. Moot under A, which makes one allocation.
4. **Cells with no deep field: skip the worklist call.** In `Fields::drop` test for any deep field
   first and go straight to the `Rc` release when there is none. The target is the 5.1-6.2% of
   time on cells freed with nothing below (5.9% on octopus, whose cells are 92% scalars).
   **Saves 0.5-1%** (guess: the `mi_free` and count test stay; the rest is the `Vec::new` and the call).
   Effort tiny, but this is the least certain number here. Not moot.
5. **Closures and paps in one allocation** (the captures inline in the `Rc` object). Closures are
   9.5% (expressions), 8.1% (scan), 9.7% (matcher), 12.6% (octopus), 5.9% (dijkstra) of time,
   making and freeing; a second of two allocations is about half of it. **Saves 4-6%** on those
   programs, 2-3% on dijkstra, and also removes the `captures` pointer load in `Instr::Captured`
   (`n1.rs`). Effort medium to large (the `Fun` layout; every `Fun::Closure`/`Pap` site;
   `FUN_CAPTURES_AT` in generated code; `sw_closure`, `sw_pap`, the machine). **Moot under A** (it is A's
   closure layout; the census put A's closure cut at about 70%), not under C or E. If A is decided,
   do not build this; if A is not, this is the largest cut here.

Not worth doing, measured:

- **Moving a unique pap's arguments out instead of cloning them** in `sw_apply_prepare`'s fast
  path (clones cost 1.0-1.8% there): only 34% (expressions), 30% (scan) and 8.5% (matcher) of the
  60.4 M, 74.9 M and 13.3 M pap calls are on a unique pap (`Rc::strong_count == 1`, from a throwaway
  counter, reverted). The saving, about one count update per argument on a third of calls, is under 0.5%.
- **The Bind nodes**: 2.3% / 2.4% of time all in (46.6 M / 43.0 M cells), 0.7% / 0.6% of it making.
  Reducing them is the effect-machinery redesign below, not a cut.

The bigger lever, not cheap: **59% of expressions' cells (190 M of 322 M) and 60% of scan's are built by
the effect runtime**, not by compiled code: `Call o r` for each skipped clause (29 M), `Bind`, `Done`, the
`Left`/`Right` renamings. They and the `Resume`s are 8.6% + 2.3% + 8.7% = 20% of expressions' time
(making and freeing, freeing **[estimated]**). That is SW-2324's "fewer cells" in the effect loop,
and it wants a design before a cut.

## Binary-trees

Making is 7.0% (all `sw_cell_new`, 68.3 M cells); freeing is 0.9% in the runtime. The frees
probably go through the cell cache and generated code, so this profile shows little for them. The memory work
there is the cells themselves, and A's cut of 62% of bytes is the lever.

## Not done

- No freeing was split below `Fun`/cell by variant on the stack (`take_children` is one function for
  all variants); the variant split is by census count.
- The census ran on the bytecode machine; native runs agree on `sw_closure` and `sw_cell_new`, but cells
  made inside the runtime were not counted natively. The runtime-built cell count is census minus native.
- 8-9% of time freeing is "not attributable"; a call-graph with inlining information (or `perf`
  on Overmind) would split it. If it is mostly cells, the cell rows are low; if closures, the closure rows are.
- No cut was built or timed.

## Commands

```
nix develop -c task profile:native -- expressions --top 60 --no-counts                          # 1 m 33 s
nix develop -c task profile:native -- scan matcher dijkstra octopus binary-trees --top 5 --no-counts
nix develop -c task profile:native -- expressions scan matcher dijkstra octopus --top 3         # with counts
nix develop -c cargo build --release -p stitchwort-cli --features stitchwort-rt/value-census --target-dir target/census
STITCHWORT_VALUE_CENSUS=out.txt target/census/release/stitchwort run <target> < input   # in aoc/ for AoC functions
python3 dev/profile_causes.py target/profile/expressions.json.gz 16 [shape]
```

The helper `dev/profile_causes.py` is new and committed with this review. The census driver (a shell
loop over the six programs) and the throwaway pap-uniqueness counter are not kept.
