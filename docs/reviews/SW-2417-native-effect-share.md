# How much of expressions and scan is still effect machinery? (SW-2417)

SW-2417, 8 Nov 2026, Sonnet lane, measurement only (no product code changed), on
`lane/SW-2417` from `main` at `47cc10dd8`. Question: natively, what share of
`expressions` (2020 day 18) and `scan` is the effect machinery, as against the parsers' own
compiled code? That bounds what operations in place stage D (native in-place
operations) and stage E (closures only when something pauses) can gain
([operations-in-place.md](../proposals/operations-in-place.md) §6).

Method: as [SW-2296](SW-2296-native-profiles.md). `task profile:native -- expressions scan
--top 45` (samply, 1 kHz, 39,105 samples for expressions; the call-counts build for the
counts), then `python3 -I dev/profile_top.py target/profile/NAME.json.gz --top 400` for the
whole self-time list, grouped by function name with a small script. Machine load average
was about 9-12 (other lanes), so only shares are used. **Time shares are measured; the
grouping is my reading of function names; everything marked *estimated* is not.** I did
not take per-group instruction counts (samply gives time only); the stage totals in
[apply-fast-paths.md](../proposals/apply-fast-paths.md) §6 are the last instruction
counts (D: expressions 483.6 G, scan 453.8 G). Time share is used as the proxy.

## 1. Self time by group (share of samples, measured)

| Group | Members | expressions | scan |
|---|---|---:|---:|
| Effect loop and leaves | `sw_eff_step`, `rt_loop`, `effect::pair`/`forwarded`/`state_step`/`skipped`/`handler_for`/`field`, `sw_state_step`, `sw_eff_begin` | 11.9% | 11.6% |
| Handler clause code | `Std.Effect.handlePlus` and its `/value` | 0.9% | 1.3% |
| Binds and closure creation | `sw_bind`, `sw_closure`, `sw_pap`, `sw_cell_new`, `sw_defer_fun` | 3.0% | 2.6% |
| Apply of runtime values | `sw_apply_prepare` 8.0%, `apply1/2/4` 5.0%, `sw_resume_begin`, `rt_resume`, `sw_cross_apply`, arity | 16.8% | 19.3% |
| Allocation, freeing, cloning | `mi_malloc`/`mi_free` 16.5%, `drop_glue<Value>` 7.4%, `value::free` 6.4%, `Fields::drop` 3.8%, `Fun::take_children` 3.1%, `Rc<Fun>::drop_slow` 2.9%, `Value::clone` 2.1%, other `Rc`/`Vec` code | 52.8% | 51.1% |
| Program's compiled code | `Std.Parse.*` (`%elim` 2.0%), `Std.List/Text.*`, `Aoc.Year2020.Day18.*` | 12.9% | 12.2% |
| Other (prims, system) | | 0.9% | 0.9% |

(Totals 99%; the remainder is below the listed tail.) The program's own code is **about
13%** of the time. Everything else is the runtime: the effect and apply machinery, and the
allocator and freeing that those make necessary.

Call counts (`call-counts` build), per run:

| Call | expressions | scan |
|---|---:|---:|
| `sw_apply_prepare` | 145.7 M | 163.5 M |
| of them: PAP fast path / closure / eager resumption / `DoneK` / `JumpK` | 60.4 / 18.8 / 29.1 / 18.6 / 18.6 M | |
| `sw_eff_step` | 141.4 M | 120.0 M |
| `sw_closure` | 106.4 M | 92.0 M |
| `sw_drop_words` | 105.5 M | 113.5 M |
| `sw_cell_new` | 85.6 M | 75.3 M |
| `sw_bind` | 46.6 M (46.4 M continuations pushed) | 43.0 M |
| `sw_apply_cached` | 63.6 M | 54.3 M |
| operations routed to a clause / forwarding skipped | 20.1 M / 29.1 M | |
| `sw_resume_begin` | 29.3 M | |

Of `sw_apply_prepare`'s calls 66.6 M (46%) are leaves and resumptions (no argument `Vec`):
the work stage D removes. 79 M (PAP fast path, closures) are applications of parser
values that stay.

## 2. Inclusive time (measured, with a caveat)

Inclusive time under the effect loop is misleading: `rt_loop` is 98-100% and `rt_resume`
34.7% (expressions), 19.0% (scan), because the continuation after a handler runs beneath
them. Usable inclusive figures: `sw_eff_step` 23.3% / 16.9%, `sw_apply_prepare` 16.8% /
20.4%, `effect::pair` 5.5% / 5.1%, `sw_closure` 3.9% / 3.3%, `sw_bind` 1.7% / 1.8%,
`sw_drop_words` 15.9% / 19.4%, `Rc<Fun>::drop_slow` (freeing closures, with what they
captured) 19.4% on expressions, `Rc<Handler>::drop_slow` 3.4%, `Resume::take_children`
1.1%.

## 3. Bounds on stages D and D+E (*estimated*)

Reasoning. A removed call is not free, so these are upper bounds. Self-time shares are
removed in full only where the work is a call that disappears.

- **D** (effect loop and resumptions become direct calls): effect loop and leaves 11.9%
  (all); the 46% of `sw_apply_prepare` calls that are leaves and resumptions, with their
  share of `apply1/2/4` (about 46% of 13% = 6-8%); the allocation of `Resume` and
  `Handler` objects and their freeing (about 2%); the handler clause (0.9%) stays. Sum:
  about 20-22% of time removed, so **at most 1.25-1.3x** on expressions; scan about the
  same (11.6 + about 9 + 2 = 22%).
- **D+E** (also bind nodes and continuation closures on the success path): add creation
  (`sw_closure`, `sw_bind`, `sw_pap`, `sw_cell_new` self time, 3.0%) and the freeing of
  closures: `Fun::take_children` 3.1% + `Rc<Fun>::drop_slow` 2.9% self, plus their share
  of mimalloc. Closures are about 40-45% of counted allocations (106 M of about 250 M), so
  about 7% of the 16.5% in `mi_malloc`/`mi_free`. About 12-14% more. Sum: 33-36% removed,
  so **at most 1.5-1.55x**. Not all of the 106 M closures go: only binds whose computation
  is `Done`, which depends on D. The parsers' own partial applications stay.

| | expressions | scan |
|---|---:|---:|
| Share removed by D (upper bound) | about 21% | about 22% |
| **D speed-up (upper bound, estimated)** | **1.25-1.3x** | **1.25-1.3x** |
| Share removed by D+E (upper bound) | about 34% | about 35% |
| **D+E speed-up (upper bound, estimated)** | **1.5x** | **1.5x** |

Check against stage C, which cut effect-loop steps 3x and time 1.1x: 11.9% of time in the
loop, cut by two thirds, is 8%, 1.09x. The shares agree with that result.

The proposal's table says D is 2-3x on expressions and scan. This measurement
puts a ceiling of about 1.3x on it, and 1.5x on D+E, unless the cost of the allocation
and freeing is also cut (section 4).

## 4. Surprises and cheaper changes

1. **Allocation and freeing is half the time (51-53%), the program's own code 13%.** Even
   with D+E, 40% of what is left would be allocation and freeing of data (lists, parser
   state, strings). Any change that frees less is worth as much as stage D:
   `drop_glue<Value>` 7.4%, `value::free` 6.4%, `Fields::drop` 3.8% self; `sw_drop_words`
   105-114 M calls, 16-19% inclusive. Reuse (`sw_drop_reuse` is only 1.1-1.8 M calls) and
   fewer cells (SW-2324) hit this directly.
2. **`Vec<Vec<Value>>::grow_one` and `finish_grow`: 3.7% inclusive, 1.4% self** on
   expressions. Something in the loop grows a `Vec` of `Vec`s repeatedly (probably the
   continuation stack or a frame list); reserving capacity once, or keeping the vectors
   across runs, is a small cheap change. Worth a ticket to find the push site.
3. **`__rust_no_alloc_shim_is_unstable_v2` 0.8% self and `__rust_alloc` 0.9%**: Rust's
   allocator front-end in front of mimalloc, which `sw_cell_new`/`sw_closure` could skip by
   calling mimalloc directly (SW-2321 inline allocation).
4. **`Value::clone` 2.1% self and `Value::data::<2>` 1.0% self (3.1% inclusive)**: building
   two-field constructors through the generic path.
5. **`sw_apply_prepare` self time is still 8% at 145 M calls (roughly 8% of time over 145 M calls).** D removes the leaf share; the PAP fast path (60 M) is the next
   candidate and would stay under D.
6. `char_value`'s thread-local `RefCell<(u32, Vec<Value>)>` shows at 0.4%: a cache hit on
   every character, small.

## 5. Not done

- No per-group instruction counts (time shares only). `task bench:compare -- --runs 1
  --runners native --instructions` would give totals but not groups.
- The "allocation" group is not split by cause beyond the closure estimate in section 3;
  samply's flat self list does not say which caller allocated. A call-graph query of
  `mi_malloc`'s callers in `samply load` would.
- Wall times were not taken (loaded machine).

## Commands

```
nix develop -c task profile:native -- expressions scan --top 45      # 3 m 45 s
python3 -I dev/profile_top.py target/profile/expressions.json.gz --top 400
python3 -I dev/profile_top.py target/profile/scan.json.gz --top 400
```
