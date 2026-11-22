# Cheaper values in the evaluator: where allocation goes, and what to change

SW-4613, 22 Nov 2026, Opus, paper lane: code, docs and the SW-4608 profiles read; nothing built
or run. Status: proposed. Follows win 5 of
[SW-4608](../reviews/SW-4608-proof-checking-speed.md) ("allocation is 27-31% of every checking
profile").

Labels: **[measured]** from the SW-4608 profile summaries
(`docs/reviews/SW-4608/profile-*-self.txt`), **[derived]** arithmetic on those, shown;
**[read]** seen in the code at `dfed0895a`, with the place; **[cited]** from a crate's own
sources, named; **[estimated]** a guess at an effect, with the reasoning; **[memory]** not
rechecked for this note.

## 0. Summary

- **The problem.** About 35-41% of the checking thread's self time is spent making, copying and
  freeing values and terms **[derived, §1]**. The biggest parts are freeing values (9-11%), the
  allocator itself (8-10%), copying a closure's environment to add one variable (2.4-4.2%), and
  cloning values (5%).
- **One correction to SW-4608.** The `Rc<[Value]>::from_iter_exact` over a `Chain` that SW-4608
  read as "appending to a spine copies it" is not the spine: it is `extend`, which copies a
  closure's whole environment every time a lambda or `let` is entered (`value.rs:1435`)
  **[read]**. Spines are already a shared `SmallVec` that grows in place when not shared
  (`Spine::push`, 0.7-0.8% self) **[read, measured]**. A persistent spine would save little; the
  environment is where copying costs.
- **The change I recommend first** (§3): two changes that cannot alter what the evaluator
  computes, because they only touch freeing and the allocator. (a) Free environments, constructor
  fields and spines the way `Shared` and `DataArgs` already are: ordinary recursion down to 128
  levels, then the iterative free (today they always go iterative). (b) Call mimalloc's plain
  `mi_malloc` for allocations aligned to 16 bytes or less, instead of `mi_malloc_aligned`, whose
  fallback over-allocates for every size that isn't a power of two.
- **What it should do.** 2-5% of check time for (a) and 0.5-2% for (b) **[estimated, §2]**, with
  kernel terms, hashes and step counts unchanged by construction. Then, measured by the same runs:
  a leaf environment built once per unfolding (2-4%), and an environment that grows in place
  (3-7%), which is unsafe code in the kernel's evaluator and needs a Fable review.
- **Not recommended:** arenas per declaration, interning, a different allocator family (§2).

## 1. Where allocation comes from

### 1.1 The profiles, by category

The SW-4608 summaries list the top 40 functions by self time on the checking thread (samply,
release build with line tables) **[measured]**. Grouping the allocation-related rows (my
grouping; the summaries have no call graph between them, so which *site* each `malloc` and
`free` serves is inferred, §1.3):

| category (self time) | tools/fmt | 2020 day 18 | 2021 day 16 |
|---|---:|---:|---:|
| freeing values: `detach`, `free_iteratively`, `take_elims`, `drop_glue::<Value/Values/DataArgs>` | 8.8% | 10.9% | 9.7% |
| mimalloc fast path: `mi_malloc_aligned`, `mi_free` | 7.6% | 7.9% | 6.3% |
| cloning values: `Value::clone`, `Vec<Value>::clone` | 5.3% | 5.3% | 5.2% |
| freeing terms: `take_children`, `Term` drop, in-place drop of `Vec<Term>` | 3.5% | 5.7% | 5.8% |
| environment copy: `Rc<[Value]>::from_iter_exact::<Chain<Cloned<…>>>` (`extend`) | 2.4% | 4.2% | 3.7% |
| `Vec<Value>` collected from a fallible iterator (`SpecFromIter` over a `GenericShunt`) | 3.3% | 2.5% | 1.9% |
| `_platform_memmove` | 2.2% | 2.0% | 2.4% |
| mimalloc slow paths (`_at_overalloc`, `_at_generic`, `realloc`), `madvise`, `finish_grow`, the alloc shim | 1.6% | 1.9% | 2.1% |
| `Spine::push` | 0.7% | 0.7% | 0.8% |
| **total** | **35.4%** | **41.1%** | **37.9%** |
| total with `StrSearcher::new` (11.7% / 1.4% / 2.9%, not allocation) taken out | 40.1% | 41.7% | 39.0% |

**[derived]** from the three `-self.txt` files. Each lists only its top 40 rows, so every figure
is a lower bound. SW-4608's 27-31% counted fewer rows (no term freeing, no `memmove`, no slow
paths). The `StrSearcher` row in tools/fmt was SW-4608's win 1 (diagnostics explained that are
never printed); with that gone, allocation is about 40% of what is left in all three.

`stitchwort_core::value::push` (1.1-1.2%) is not a spine push: it is the machine's frame push
with its depth check (`value.rs:1535`) **[read]**, so it is left out above.

### 1.2 The sites, from the code

Ranked by the profile share each one can be tied to:

1. **Freeing (9-11%).** Every `Values` (constructor fields, closure environments) and every
   `Spine` whose last reference goes always takes the iterative free (`value.rs:683-710`): a
   thread-local `EMPTY` and `PENDING` lookup, a `RefCell` borrow, every value moved onto the
   work list, then `detach` on each. `Shared` and `DataArgs` instead recurse normally down to
   `NESTING_LIMIT = 128` and only then go iterative (`drop_nested`, `value.rs:220`). That split
   is history: SW-2482's first version made `DataArgs` and `Shared` always iterative too and
   cost 1.3-1.6% of `check --no-cache`; the depth counter brought it to 0.2-0.6%
   (`docs/performance/log.md`, SW-2452/2468/2482) **[read, measured there]**. `Values` and
   `Spine` were never given the depth counter, and they are freed far more often.
2. **The allocator (8-10%).** Already mimalloc (§2.6). Of its time, `mi_malloc_aligned` and
   `mi_free` are the fast paths; the slow aligned paths show at 0.5% each in all three profiles,
   which they should not for 8-byte alignment (§2.6).
3. **Cloning values (5%).** Inherent where a value is shared (a variable read from the
   environment, `value.rs:1584` and `1614`). Avoidable ones: `case_tree` clones every argument
   out of the spine into a `Vec` even though it keeps the spine too (`value.rs:2767`), `branch`
   clones a constructor's fields with `fields.to_vec()` even when it holds the only reference
   (`value.rs:2394`), and `extend` clones the whole environment (next item). A `Value` is about
   56 bytes **[estimated from the field types: `Pi` holds a `Name` (`Rc<str>`, 16), an `Icit`, a
   `Shared` (8) and a `Closure` (a 16-byte `Rc<[Value]>` and an 8-byte `Rc<Term>`); not measured,
   a `size_of` assertion would settle it]**, so each clone is a 56-byte copy plus a reference
   count bump.
4. **Freeing terms (3.5-5.8%).** Read-back builds `Term`s that the elaborator compares, searches
   and drops (`quote_as_until` 2.5-3.2% self, 37% inclusive in tools/fmt). Today's read-back work
   (SW-4635, SW-4637) cuts how much is read back, which shrinks this directly; it is not a value
   representation question.
5. **Copying environments (2.4-4.2%, plus their `malloc`/`free`).** `extend` (`value.rs:1435`)
   builds a new `Rc<[Value]>` of length n+1 for every lambda entered (`enter`), every `let`
   (`value.rs:1710`, `1713`, `1949`): O(n) per binder, quadratic in a body's binders. SW-3726
   already batched a solution's run of lambdas (`enter_run`, `value.rs:957`); everything else
   still copies.
6. **Case-tree environments (1.9-3.3% for the `Vec` collect, part of `memmove`).** Unfolding a
   definition: the arguments cloned out of the spine into a `Vec` (`case_tree`, a
   `collect::<Option<Vec<_>>>`, which is the `GenericShunt` row), each `case` appending its
   fields (`env.extend(fields)`, growing the `Vec`: `finish_grow`, `realloc`), and at the leaf
   `env.into()` (`value.rs:1511`) copying the `Vec` into a fresh `Rc<[Value]>` and freeing the
   `Vec`: two allocations and a `memmove` where one would do.
7. **Spines (0.7-0.8%).** `Spine` is `Option<Rc<SmallVec<[Elim; 2]>>>` (`value.rs:525-533`):
   empty spines allocate nothing, pushes grow in place unless shared (`Rc::make_mut`), and the
   first two eliminations share the allocation with the count. A shared spine is copied on push,
   but nothing in the profile shows that as large.

### 1.3 What is inferred

The summaries give self and inclusive time per function, not who called `malloc` or `free`, so
the split of the allocator's 8-10% among the sites is not known. That `from_iter_exact` row is
`extend` is from its type (the only `Rc<[Value]>` collected from a `Chain` of cloned values and a
`once` in `crates/core`, `value.rs:1437`) **[read]**. How long environments are when extended,
and how often the extended environment has no other owner, is not known either; §3 step 0
measures both before step 3 is designed in detail.

## 2. Options

Each option is judged by: what changes in `value.rs`, whether kernel behaviour or terms could
change (they must not), how to show they don't, and its size. The equivalence checks are the
same for all (§2.8).

### 2.1 Bounded-recursion free for `Values` and `Spine`

- **Change.** `Drop for Values` and `Drop for Spine` use `drop_nested`, as `Shared` and
  `DataArgs` do: free by ordinary recursion while fewer than 128 drops are nested, then hand the
  rest to `free_iteratively`. Optionally a quicker test first: a sequence whose values are all
  atoms (`is_atom`, extended to `Neutral` with an empty spine, `Nat`, `Sort`) drops with no
  bookkeeping at all.
- **Behaviour.** Freeing has no effect on any result: no `Drop` in `value.rs` reads or writes
  evaluator state (`Unfolding`'s drop only frees its kept value and its base chain,
  `value.rs:368`) **[read]**. Terms, hashes and steps cannot change. The risk is stack depth,
  bounded the same way as today's `Shared` path.
- **Tests.** The seven `freeing_a_deep_*_does_not_overflow_the_stack` tests in `value.rs`'s unit
  tests (256 KB threads), which cover spines, closure environments and unfolding chains.
- **Saving.** 2-5% **[estimated]**: making `DataArgs`/`Shared` always iterative cost 1.3-1.6%
  (measured, SW-2482), and `Values`/`Spine` are freed far more often (every environment,
  constructor and stuck application); the freeing rows total 9-11%.
- **Size.** Small: about 30 lines. No unsafe code.

### 2.2 A plain `malloc` for small alignments

- **Change.** Not in `value.rs`: in the CLI's and `stitchwort-test-alloc`'s `#[global_allocator]`,
  a 20-line `GlobalAlloc` that calls `mi_malloc`/`mi_zalloc`/`mi_realloc` when `layout.align()
  <= 16 && layout.align() <= layout.size()`, else the aligned calls, and `mi_free` always.
- **Why.** `mimalloc::MiMalloc` sends every allocation to `mi_malloc_aligned` (mimalloc 0.1.52,
  `src/lib.rs:50`) **[cited]**. In mimalloc v3 that takes the fast path only if the size class's
  page has a free block ready; otherwise it goes to `_at_generic`, which uses the normal path
  only when the size is "naturally aligned" (a power of two up to 4 KiB), and else
  over-allocates `size + alignment - 1` bytes in a larger size class (`_at_overalloc`)
  (libmimalloc-sys 0.1.49, `c_src/mimalloc/v3/src/alloc-aligned.c`, lines 18-28, 153-181 and
  185-231) **[cited]**. Our allocations are mostly not powers of two: an environment of n values
  is 16 + 56n bytes **[estimated]**. Plain `mi_malloc` already returns 16-byte-aligned blocks for
  sizes of 16 or more (`MI_MAX_ALIGN_SIZE 16`, `include/mimalloc/types.h:38`; the assertion at
  `src/alloc.c:52`) **[cited]**, which is what Rust's `System` allocator relies on for its own
  `malloc` path **[memory]**.
- **Behaviour.** None: allocation addresses never reach a result. (`Spine::addr` and
  `shared_key` use addresses as identities while a value is held, never as an order that
  decides anything **[read, `value.rs:557-575`]**; a review should confirm no hash map keyed by
  address is iterated in an order that reaches output.)
- **Saving.** 0.5-2% **[estimated]**: the two slow-path rows are 1% together, plus fewer
  refills and a smaller footprint from not over-allocating.
- **Size.** Small. Also worth one A/B at the same time: mimalloc's `v2` feature (the crate
  defaults to v3, `README.md` "Usage with v2", `build.rs` lines 8-12 **[cited]**), a one-line
  change.

### 2.3 Build a leaf environment once per unfolding

- **Change.** `Control::Tree` and `branch` keep the arguments in the spine they already hold
  and collect only the fields bound so far; a variable in a case-tree node is looked up in the
  fields first, then the spine's arguments. At a leaf the body's environment is built in one
  `Rc<[Value]>` straight from both (`from_iter_exact` over a known length), instead of a `Vec`
  copied into an `Rc`. `branch` moves a constructor's fields out when it holds the only reference.
- **Behaviour.** The environment's contents and order are the same; only how it is built
  changes. Terms and steps unchanged if lookups agree, which the reference evaluator and the
  step counts check (§2.8). The care needed is in index arithmetic (a `case` refers to its
  scrutinee by index from the end of the environment, `value.rs:1472`).
- **Saving.** 2-4% **[estimated]**: the `Vec` collect row (1.9-3.3%), part of `memmove`, and
  one allocation and free per unfolding.
- **Size.** Medium: about 150 lines in `value.rs` (`Control::Tree`, `Frame::Scrutinee`,
  `branch`, `stuck_tree`, `walk_tree`). Kernel evaluator: Fable review.

### 2.4 An environment that grows in place

- **Change.** `Env` stops being `Values` (which constructor fields keep) and becomes its own
  type: a shared buffer of fixed capacity plus a length, `{ buf: Rc<EnvBuf>, len: u32 }`. A view
  sees `buf[..len]`. Extending writes in place when this view's length is the buffer's filled
  length and there is room; otherwise it copies into a new buffer of twice the capacity, as
  today. Values past a view's length belong to the buffer and are freed with it. The buffer is
  never reallocated, so a slice handed out by one view stays valid while another view appends
  past it; that invariant, and single-threaded use (values are `Rc`, not `Send`), are what make
  the `UnsafeCell` sound.
- **Behaviour.** Every lookup returns the same value it does today; terms and steps unchanged.
  Two costs to watch: memory held longer (an abandoned branch's values stay alive while a
  shorter view of the same buffer lives, e.g. in a closure kept in a meta solution), so peak
  memory is part of the measurement; and unsafe code in the kernel's evaluator.
- **Saving.** 3-7% **[estimated]**: `extend`'s 2.4-4.2% and its share of `malloc`/`free` and of
  freeing, if most extensions hit in place, which step 0 measures. If most environments turn out
  shared at the point of extension, this option drops to near nothing and should not be built.
- **Size.** Medium-large: a new type with its drop, `Closure.env`'s type, and the 57 places
  outside `value.rs` that build a `Closure` (`grep -rn "Closure {" crates/*/src`, mostly in
  `elab`). Kernel evaluator and unsafe code: design detail first (a short addendum to this
  note), then Fable review of the code.
- **Alternatives considered.** A persistent linked environment (`Rc<(Value, Env)>`, as smalltt
  does **[memory]**) makes extending O(1) always but lookups O(index), and every `env.len()` and
  slice use in the machine would change; worse for the many short lookups. A small inline
  environment (`SmallVec` inside the `Rc`, as the spine does) helps only if environments are
  very short, which step 0 also answers.

### 2.5 A smaller `Value`

- **Change.** Bring `Value` from about 56 to 32-40 bytes: a `Closure` as one pointer
  (`Rc<ClosureInner>` holding environment and body), binder names out of `Pi`/`Lam` (into the
  term, or interned), a constructor index as `u32`. Every clone, environment copy, spine slot
  and `memmove` gets cheaper in proportion.
- **Behaviour.** Representation only, but it touches every match on `Pi`, `Lam` and `Ctor` across
  `core` and `elab`. Names matter to printing, which must not change.
- **Saving.** 3-6% **[estimated, weakly]**: clone, copy and `memmove` rows are about 10%
  together; a third fewer bytes moved. compact-values.md (SW-2324) found for native code that
  smaller values paid only through instructions removed; the same caution applies.
- **Size.** Large. After steps 1-3, and only if a `size_of` check confirms the 56 bytes.

### 2.6 A different allocator

The CLI already uses mimalloc (`crates/cli/src/main.rs:1111`, `mimalloc = 0.1.52` with default
features in the workspace `Cargo.toml`), and every test binary does too through
`stitchwort-test-alloc` (`docs/testing.md`, "Allocator") **[read]**. It is mimalloc v3.3.2,
compiled from the sources bundled in `libmimalloc-sys` 0.1.49 (`c_src/mimalloc/v3/include/
mimalloc.h:11`, `MI_MALLOC_VERSION 30302`), not from Nix **[cited]**. cell-allocator.md
(SW-2360) already argued for keeping mimalloc rather than writing our own. jemalloc (through
`tikv-jemallocator`) is not expected to beat mimalloc on small, short-lived, single-threaded
objects **[memory]**, and nothing in these profiles points at mimalloc's own algorithm: its fast
paths run at a few ns each (cell-allocator.md §1 measured 2.7 ns per allocation and 3.4 ns per
free on binary-trees). The work is the number of allocations, not their price. So: §2.2's
wrapper and a v2 A/B, no switch.

### 2.7 Arenas per declaration, interning

- **Arena per declaration** (`bumpalo` is already in the lock file). Values escape a
  declaration: kept unfoldings (`Rc<Unfolding>`), metavariable solutions, conversion memos, the
  elaborator's caches. An arena needs lifetimes on `Value` or a copy-out at every escape. Large
  and invasive, with use-after-reset as the new failure mode in the kernel. Not recommended.
- **Interning / hash-consing.** Values hold closures and mutable unfoldings, so interning them
  is out. Hash-consing read-back terms would cut term building and freeing (3.5-5.8%) but adds
  a hash per node, and the read-back work in progress (SW-4635, SW-4637) is shrinking the same
  cost by not reading back. Not now.

### 2.8 Showing kernel behaviour is unchanged

For every option above, all must hold:

1. **Steps identical, declaration by declaration.** `--timings=all` reports steps per
   declaration; steps are counted per machine step (`g.machine.budget.step()`, `value.rs:1446`),
   which none of these changes alters. Compare before and after on the namespaces of §3; any
   difference is a bug.
2. **Kernel terms identical.** The `hash_stability` snapshots (prelude, examples, projects)
   unchanged, run by the verifier.
3. **The reference evaluator agrees.** The differential tests (`crates/driver/tests/proofs/
   differential.rs` and the `reference`-feature tests in `crates/core/tests/it/`), which compare
   the machine with the recursive evaluator in `reference.rs`.
4. **The other evaluation modes still agree.** The same step comparison under `STITCHWORT_GLUE=0`
   and `STITCHWORT_DEBUG_FORCE_UNGLUED=1` on one namespace, since they take other paths through
   `force` and the case-tree code.
5. **Stack safety.** The seven `freeing_a_deep_*` unit tests.
6. **Broadly, after merging.** Overmind's rolling check, then `fuzz:kernel` and `fuzz:elab` in
   compute mode.

Changing `value.rs` changes the evaluation fingerprint, so check caches start afresh; that is
expected.

## 3. Recommendation

**Step 0, measure (with step 1, one lane).** Two counters behind an environment variable, as
`STITCHWORT_MATCH_METRICS` is: at `extend`, a histogram of environment length and the share whose
environment has no other owner (`Rc::strong_count == 1`) or whose buffer would have room; and a
`size_of::<Value>()` / `size_of::<Elim>()` printout. These decide whether §2.4 is worth building.

**Step 1, low risk (Sonnet, about an hour of agent time).** §2.1 (bounded-recursion free for
`Values` and `Spine`) and §2.2 (plain `mi_malloc` for small alignments), as two commits measured
separately, plus the v2 A/B as a measurement only. Neither can change what is computed; §2.1
lives in `value.rs` but only in `Drop`, and §2.2 is outside the kernel. Review: Opus, not Fable.

**How to measure.** In the lane, on two or three named namespaces, the way SW-4637 measured:
`check NS --no-project-cache --timings=all` from `tools/fmt` (for example
`Syntax.ReadBackHungApp`, 17K declarations with imports) and one AoC day
(2020 day 18's proofs namespace), under `/usr/bin/time -l`, at least 5 runs each (hyperfine), load
noted. macOS's `time -l` also reports instructions retired, which a loaded machine disturbs
much less than wall time **[memory]**; use it as the main figure, user time second, and maximum
resident set size for memory. **A win** is 2% or more fewer instructions or less user time with
total steps identical; under 1% is noise (SW-2482's runs put noise at about 0.5%). The SW-4608
whole-project runs (tools/fmt `check --no-cache`, the two AoC days) are whole-project checks:
they go to the verifier or Overmind after merging, not to the lane. Each step gets its
performance-log entry (D3444).

**Step 2 (Opus, Fable review).** §2.3, the leaf environment built once. Measured the same way.

**Step 3 (Opus, Fable review), only if step 0's counters say most extensions could happen in
place.** §2.4, the environment that grows in place: a short design addendum here first (the
buffer's invariant, its drop, the memory it holds), then the code.

**Later, if steps 1-3 leave the clone and copy rows large:** §2.5, a smaller `Value`.

**What needs a Fable review before merging:** steps 2 and 3 (they change how the kernel's
evaluator builds the environments it looks variables up in; step 3 adds unsafe code there).
Step 1 does not change evaluation and needs the usual Opus code review. Nothing here needs a
decision from Matt: it is optimisation with results, messages, hashes and proofs unchanged
(D3447). If step 3's memory measurement shows peak memory rising noticeably, that trade is
brought to him.
