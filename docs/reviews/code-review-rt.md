# Code review: `crates/rt`, the fast runtime (SW-1871)

Read on `lane/SW-1871` at `d4bff5a5c`, 7 Nov 2026. **Reading only: nothing was built or
run.** Scope: the machine (`machine.rs`), compilation to it and in-place reuse
(`code.rs`), `opt.rs`, values and reference counting (`value.rs`), the effect runtime
(`effect.rs`, `run.rs`), arrays and the other natives (`prims.rs`, `natives.rs`), the
native ABI (`native_abi.rs`, `native_aot.rs`, `linked.rs`), the codec and validator, the
profiler, and every `unsafe` block in the crate (252 in `native_abi.rs`, 6 in
`native_aot.rs`, 2 in `prims.rs`). Where a finding depends on `crates/native` (the code
generator on the other side of the ABI), I read only the parts the ABI's contracts
lean on, and say so.

## Summary

The runtime is in good shape. Its soundness argument is clear and mostly enforced
rather than just stated. The machine has no `unsafe` at all. Every in-place change it
makes (reuse tokens, array `set`/`push`/`pop`, freeing) is gated by a run-time
`Rc::get_mut` or strong-and-weak-count check. So no bookkeeping bug in `code.rs`
(liveness, `MOVE` marks, tokens, known constructors) can make it change a shared value:
the worst outcome is a lost reuse or a read of `Erased`. The one deliberate write into a
shared cell, TRMC's hole fill, is argued, Miri-tested and confined to a loop no one else
can observe. All three findings of the 1 Nov review in this crate have been fixed: the
padding read (SW-1122), the missing runtime in the test fingerprint (SW-1123, SW-1329),
and the owning-looking native API (SW-1124). What remains is smaller: one disagreement
between the machine and native code (`Array.replicate`'s cost), two ways a valid program
can still crash the process rather than hit a limit (dropping deeply nested arrays, text
that doubles), and one half of the 1 Nov boundary finding: native compilation still
trusts a publicly constructible `Image` to agree with its program.

**Top five recommendations**

1. Charge `Array.replicate`'s count in native code as the machine does (F1). Without it
   a run counts differently on the two runners, and a huge count aborts natively on
   allocation instead of stopping with `Work`.
2. Free directly nested arrays with the work list, as `Fields`, `Fun` and `Delay` already
   are (F2). An unboxed one-field record of an array makes `Array (Array …)` chains of
   any depth possible, and dropping one recurses in Rust.
3. Make an `Image` constructible only by `code::compile`, or have native compilation
   take the program and build the image itself (F3). Today a safe caller can hand
   `n1::compile` any image, and the generated code trusts its register and table indices.
4. Bound what `Text.append` can allocate per step, at least in the counterexample
   search's `number_words` mode (F4, D2660). Forty doublings of a text ask for a terabyte
   and abort the compiler, which SW-907 fixed for numbers but not for text.
5. Give `code.rs`'s compiler and the validator the nesting guard the optimiser already
   has (F5). They recurse over every body, including the ones `opt.rs` skips for being
   too deep.

**Findings by severity:** high 0, medium 4, low 8.

## Findings

| # | Where | What | Sev | Conf | Size |
|---|---|---|---|---|---|
| F1 | `machine.rs:575`, `:1184`; `native_abi.rs:1547` (`sw_prim`), `:1898` (`sw_apply_prepare`) | Native code doesn't charge `Array.replicate`'s count; the machine does | medium | high | M |
| F2 | `value.rs:37-53`, `:244-273`, `:337-361` | A `Value::Array` dropped outside `free` drops its elements by recursion; directly nested arrays overflow the stack | medium | medium | S |
| F3 | `code.rs:258-267` (`Image`'s pub fields); `crates/native/src/n1.rs:441` | Native compilation trusts any `Image` and any program/image pairing from safe code | medium | medium | M |
| F4 | `prims.rs:633-645` (`TextAppend`), `prims.rs:373` (`number_cost`) | A text can double every step; nothing charges its size, even in `number_words` mode | medium | medium | M (D2660) |
| F5 | `code.rs:376-419` (`fill`), `:421-460` (`builds`), `:613` (`expr`); `validate.rs:70` | Unguarded recursion over bodies that `opt.rs` deliberately skips for depth | low | low | S |
| F6 | `machine.rs:528-532`, `:1252-1270`, `:358-362` | Tail over-application nests `Ret::Apply` without counting a frame; a long chain is dropped by recursion on failure | low | medium | S (D2661) |
| F7 | `profile.rs:285-300` | If the timer thread can't start, the profiler samples once, not "at every entry" | low | high | S |
| F8 | `machine.rs:1284-1351` vs `native_abi.rs:1429-1545`; `machine.rs:366` vs `native_abi.rs:1715`; `unique` ×3 | The reuse instructions, `function_value` and `unique` are hand-mirrored copies | low | high | M |
| F9 | `native_abi.rs:1404` (`sw_free_emptied`), `:1510` (`sw_empty_cell`); `prims.rs:968` | Contract-only helpers have no debug check of uniqueness; the hole-fill check is debug-only | low | high | S |
| F10 | `validate.rs:186-192` | An arm may bind the same field twice; `Unpack` then gives the second slot `Erased` | low | high | S |
| F11 | `run.rs:294-297` | The library prints the array-copy note to the process's stderr itself | low | high | S |
| F12 | `profile.rs:265-281` | Each sample walks every frame depth: O(depth) per sample under deep recursion | low | medium | S |

## Details

### F1. Native code doesn't charge `Array.replicate` (medium, high)

SW-1637 (`2a3b2fd26`) made the machine charge `Array.replicate count _` its count in
steps before allocating, "so a huge count … runs out of steps instead of asking for the
memory". It did this in both machine paths: the direct `Prim` (`machine.rs:1184-1187`)
and a function value entered through `enter` (`machine.rs:575-581`). Native code reaches
the same operation through `sw_prim` (`native_abi.rs:1547`) or, as a function value,
`sw_apply_prepare` (`:1898`). Both call `prims::eval` directly, and nothing in
`crates/native` mentions `replicate` (grep: no hits).

- **Agreement.** The module comment promises "a run counts the same whichever runner did
  the work" (`native_abi.rs:32-36`). A program calling `Array.replicate (count := 10⁶)`
  takes a million more steps on the machine than natively, so a step limit between the
  two counts fails on one runner and passes on the other.
- **Robustness.** With `count := 10¹²`, the machine stops with `ResourceError::Work`. A
  native run calls `vec![x; 10¹²]` inside an `extern "C"` helper, which aborts the
  process on allocation failure ("limits fail, never choose", D2543).

**Fix (M, Sonnet):** a helper `sw_charge(context, cost) -> u64` that adds to the
context's steps and sets `OUT_OF_STEPS`, called by generated code before a replicate
`Prim`, plus the same check in `sw_apply_prepare`'s native branch. Add an agreement
test: the same program's steps on both runners, and a huge count stopping with `Work` on
both. Run `rt`'s `native_abi` and `crates/native`'s step-count tests.

### F2. Directly nested arrays are freed by recursion (medium, medium)

`value.rs`'s module comment says "Freeing never recurses … (`Drop` for `Fields`, `Fun`
and `Delay`)". `Value::Array(Rc<Vec<Value>>)` has no such `Drop`. `take_children` handles
an array met inside `free`'s work list (`value.rs:265-269`), but an array dropped
anywhere else (a register overwritten, `release`, `regs.clear()` after a failure) goes
through Rust's drop glue: `Rc<Vec<Value>>` drops each element, and an element that is
itself `Value::Array` recurses. A `Data` element is safe: `Fields::drop` switches to the
work list.

This is reachable because a record with one run-time field is stored unboxed
(`Data::unboxed_field`, `core/src/globals.rs:553`). A type like `structure Rose where
children : Array Rose` is then a bare `Value::Array` whose elements are bare
`Value::Array`s, and a path a million deep (built by a loop) overflows the stack when it
is dropped. I didn't check that the kernel admits that nested inductive (hence medium
confidence). If it doesn't, the same shape arises from any recursion through
`Array (Array …)` that a future unboxing admits.

**Fix (S, Sonnet):** wrap the buffer as `Items(Rc<Vec<Value>>)`, `repr(transparent)`
(the address at byte 8 is unchanged, so `probe_layout` and native code are unaffected),
with a `Drop` like `Fields::drop`. Add a case to `a_long_list_is_freed_without_recursing`:
two million directly nested arrays.

### F3. Native compilation trusts any `Image` (medium, medium)

SW-1124 fixed the lifetime half of the 1 Nov finding (§1.3): `n1::compile` takes the
`Image` by value, `Islands` owns it and the module privately, the crossing is dropped
first, and `Crossing::new` is `unsafe` with a precise contract. The other half, "the same
family of APIs also lets a caller supply code, an image and an outline separately, with
their agreement enforced by convention", is still open at the `rt` boundary:

- `Image`'s fields are all `pub` (`code.rs:258-267`), as are `Code`'s (`:245-255`), so
  safe code can build an image with any instructions, register numbers, tables and
  operand lists.
- `n1::compile(program: &Program, image: Image, …)` is a safe function that pairs the
  two. Nothing checks that `image` came from `code::compile(program)`, and `Audit`
  checks only that the code embeds no host address.
- Generated code indexes frame slots, jump tables and `Tables` by the image's numbers.
  An out-of-range register or a mismatched program (another program's shapes or arities)
  gives native code that reads or writes outside its frame or a cell. That is undefined
  behaviour reachable from safe Rust. On the machine the same mismatch only panics:
  safe indexing.

The CLI always builds the image with `code::compile` just before, so this is an API
soundness gap, not an observed bug. I didn't trace exactly what `n1` emits for an
out-of-range index, hence medium confidence.

**Fix (M, Opus: unsafe boundary):** make `Image` and `Code` fields private with
read-only accessors, so `code::compile` is the only constructor, and give `n1::compile`
a `Compiled` value (program and image together, made by one function) instead of the
two separately. `TableStore::new` and `Outline::of` then take that value too.

### F4. Text growth is unbounded per step (medium, medium; D2660)

`TextAppend` (`prims.rs:633-645`) allocates `a.len() + b.len()` in one native call, so
`t ++ t` doubles a text in one step: forty doublings ask for a terabyte. The step limit
can't stop this. Memory isn't a resource limit, so the result is an allocation abort,
not a `ResourceError`. SW-907 solved exactly this for numbers in the counterexample
search (`Limits::number_words`: "a random number at a word's edge … makes numbers of
gigabytes in a few steps"), and SW-1637 for `Array.replicate`. `number_cost` returns 0
for every text operation, so a property such as `∀ n, (double n "a").length = 2 ^ n`
with a search-chosen `n` of 64 aborts the checker.

**Recommendation:** in `number_words` mode, charge `TextAppend` (and `TextJoin`, which is
linear in its output) one step per 8 bytes of result, before allocating. That is the
same rule as numbers: it bounds time and memory by steps. Whether `run` should also have
a memory limit, or this charge everywhere, is D2660. Size: M (prims, the machine's two
charge sites, a test in the search's suite).

### F5. Unguarded recursion in `code.rs` and the validator (low, low)

`opt.rs`, `trmc.rs` and `specialise.rs` skip a body nested more than 1,000 deep "so that
nothing runs away" (`opt.rs:229-234`), and `lower.rs` checks its stack at every level.
But `code::compile` (`Compiler::expr`), its `fill` and `builds` helpers, and
`Program::validate` all recurse over every body with no guard, including exactly the
deep bodies the optimiser declined. Lowering's stack check is against lowering's own
frames. `Compiler::expr`'s frames are probably larger (several `Slots` clones per
level), so a body that lowering just accepts may still overflow when compiled. The
likeliest real source is a long `let` chain (a long `do` block), since long list
literals are already compact (`erasure.rs:131`). `builds` is also called at every
`Match` arm and dead slot, so it's O(n·d) on a deep body.

**Fix (S, Sonnet):** check `opt::nesting` in `code::compile` and `validate`, and either
compile a too-deep body with an explicit work stack or report it as a lowering error
(not a crash). Test with a 50,000-deep `let` chain on a 2 MiB thread.

### F6. Pending over-applications aren't frames (low, medium; D2661)

`TailApply` of a function given more arguments than it takes pops the frame and pushes
the callee with `Ret::Apply(rest, frame.ret)` (`machine.rs:1264-1269`, `:528-532`). If
the callee also tail-over-applies before returning, the `Ret` nests again, while
`frames.len()` stays the same. So the chain of pending applications grows with no frame
counted (`enter_frame` sees one frame). It is bounded only by the step limit (10¹⁰).
The reference evaluator presumably counts these as pending work (I didn't check `core`),
so the two can disagree on `Depth` against `Work`. On failure, `release_failed` (`frames.clear()`) drops the chain by
recursion through `Box<(Vec<Value>, Ret)>`. A few hundred thousand levels overflow an
8 MiB stack. Making such a chain needs a function whose body over-applies itself in tail
position, which takes a dependent type (`f : (n : Nat) → F n`), so this is unlikely in
practice. `Ret::Then`, `Ret::Eff` and `Ret::Step` nest the same way.

**Fix (S):** count a `Ret` that wraps another `Ret` against the frame limit (D2661), and
drop `Ret` chains iteratively (a `Drop` for `Frame` that unlinks).

### F7. The profiler's fallback samples once (low, high)

`timer` (`profile.rs:285-300`) says "No timer: sample at every entry rather than never",
and sets the flag once. `entered` clears the flag at the first sample (`:252`), and with
no thread nothing raises it again. So a run whose timer thread can't be spawned (thread
limits, or a WebAssembly build if `--profile` is ever offered there) gets exactly one
sample. **Fix (S, DeepSeek):** return `None` from `timer` on failure and fall back to
`Sampling::EachEntry`'s behaviour. Unit-test the fallback by injecting the failure.

### F8. Hand-mirrored logic between the machine and native helpers (low, high)

`sw_ctor_reuse`, `sw_unpack` and `sw_drop_reuse` (`native_abi.rs:1429-1545`) are line
for line the machine's `CtorReuse`, `Unpack` and `DropReuse` (`machine.rs:1284-1351`).
`NativeRun`'s `function_value` (`native_abi.rs:1715`) is `State::function_value`
(`machine.rs:366`), and `unique` is written three times (`machine.rs:1488`,
`native_abi.rs:1456`, inline in `value.rs:339`). The helpers' header says "Each does
exactly what the machine's instruction does, in the same order", which is true today and
held only by care. `effect.rs` already shows the better pattern: `state_handler` and
`handler_for` are "shared with native code's … so the two can't drift". **Fix (M,
Sonnet):** move the three reuse operations into functions on values
(`reuse::unpack(cell, pairs, put) -> Option<Value>` and so on) that both call, and one
`unique` in `value.rs`. The trace agreement tests (`alloc_trace.rs`) guard the refactor.

### F9. Contracts the helpers could check in debug builds (low, high)

`sw_empty_cell` (`native_abi.rs:1510`) writes `Erased` over `n` fields at a raw address
it's told is a unique cell, and `sw_free_emptied` (`:1404`) frees a cell as
`MaybeUninit` on the promise that it is unique and every field was moved out. If that
promise is ever wrong (a codegen bug in `n1`'s inline `Unpack`), the first drops a value
someone else owns and the second leaves two owners of moved fields. Both are silent
use-after-free. Neither checks anything, though a `debug_assert!` that the strong count
is 1 and the weak count 0 costs nothing in release and runs under every native test.
Similarly `prims::fill`'s check that the hole still holds `Erased` (`prims.rs:968`) is a
`debug_assert`. In release a second fill would leak the first value and change a list
someone holds. That is a wrong answer, not undefined behaviour, but cheap to make loud.
**Fix (S, DeepSeek):** the two debug assertions, and `assert!` in `fill`.

### F10. The validator accepts a field bound twice (low, high)

`validate.rs:186-192` checks that each `(field, slot)` of an arm names a real field, but
not that each field is bound once. For `[(0, a), (0, b)]`, `Unpack` on a unique cell
moves field 0 into `a` and then reads `Erased` into `b`, on the machine
(`machine.rs:1319-1321`) and natively (the same in `sw_unpack`, and `n1`'s inline unpack
erases as it goes). Nothing I read produces such an arm: `opt.rs`'s `match_` only adds
missing indices. But the codec says any bytes it accepts give a program "that
`Program::validate` accepts", and the machine's correctness assumes distinct fields.
**Fix (S, DeepSeek):** reject a repeated field index, with a codec test.

### F11. The runtime prints to stderr itself (low, high)

`run_on` (`run.rs:294-297`) calls `eprintln!` for the array-copy note. Every host that
runs `main` through it gets the line on the process's stderr whether or not it has one:
tests, the language server (where stderr is the log) and the playground (the console).
Every other message goes back to the caller. **Fix (S):** return the note with the
outcome (or through the `Terminal`), and let the CLI print it.

### F12. Profiler samples cost O(depth) (low, medium)

`Profiler::sample` (`profile.rs:265-281`) walks `chains[..=depth]` on every sample. At a
million pending frames (within the 2M limit) and a 1 ms interval, each sample costs about
as long as the interval, so profiling a deep recursion can double its run time and skew
what it reports. **Fix (S):** keep a running per-row "on stack" count, updated on push,
pop and tail replace, so a sample is O(rows touched), or cap the walk and say so in the
report.

## Checked and sound

**Unsafe code (every block in the crate).**

- **Layout reads** (`native_abi.rs` `words`, `allocation`, `counts_at`, `fun_key_at`,
  `probe_functions`): each reads only bytes its variant initialises. The padding read the
  1 Nov review found is gone (SW-1122): `fun_key_at` reads the variant byte and the `u32`
  at offset 4 separately. A `cfg(test)` const block makes the constant evaluator reject a
  whole-word read, and the probe test is Miri-ready. `Value` and `Fun` are `repr(u8)`, so
  their own layout is defined. The `Rc` and fat-pointer layout is std's, unchanged by
  design, and checked once per process before any native code runs.
- **`from_words`**: writes three words into `MaybeUninit<Value>` and assumes it
  initialised; sound for words that came from a valid value (padding may be anything).
- **Ownership across the crossing** (`Crossing::enter`, `apply`, `step`, `finish`):
  `ManuallyDrop` for moved-in values, `set_len(0)` before freeing the argument buffer,
  `assume_init` only after the trampoline wrote a whole value. Sound given
  `Crossing::new`'s contract.
- **Lifetimes** (SW-1124): `Crossing::new` is `unsafe` with the contract stated; `Islands`
  owns the module and the image privately and declares the crossing first, so it drops
  first. The standalone executable's tables live for the process. `TableStore` owns five
  boxes and frees each once. The shapes are copied, which fixed NO7's stack-copy bug.
- **`NativeRun` pointer** (`Context::run`): made from a `&mut` that isn't used while
  native code runs, and never escapes the call. Helpers never call program code, so there
  is no re-entrant `&mut`.
- **Stack** (`thread_stack_low`, `NativeExecutor::stack_floor`): the floor is an absolute
  address checked against the thread's real stack with margins, fixed at the first
  crossing; the executor is `!Send`. A later, deeper crossing only has less room, never
  more.
- **Cell helpers** (`sw_ctor`, `sw_ctor_reuse`, `sw_unpack`, `sw_drop_reuse`,
  `sw_free_emptied`): `new_uninit_slice` with a bitwise copy and then `assume_init`;
  reuse only after `strong == 1 && weak == 0`. The `MaybeUninit<Value>` cast in
  `sw_free_emptied` keeps the allocation's layout. Nothing in `rt` makes a `Weak`, so
  the weak test is belt and braces.
- **Effect leaves** (`handler_taken`, `resume_taken`, `sw_eff_*`, `sw_resume_begin`,
  `sw_unwind_*`, `sw_defer_fun`, `sw_drop_deferred`): every `into_raw` has one matching
  `from_raw` on each path, and a deferred function value is dropped even after an error
  (`NativeExecutor::cross`).
- **Panics in helpers** abort rather than unwind into compiled code: explicitly through
  `internal()`, and implicitly because a panic in an `extern "C"` function aborts. The
  mixed style is cosmetic.
- **`native_aot::Manifest`**: `Sync` for read-only static data; `data()` is `unsafe`
  with its contract.
- **`prims::fill`** (TRMC hole fill): follows the `get_mut_unchecked` rule, with a pointer
  from `Rc::as_ptr` (write provenance) and a Miri test under both borrow models. The
  exclusivity argument in `trmc.rs`'s module comment holds: holes are made and filled by
  one loop, effect continuations are heap data, and the runner's captures never include a
  function's frames.

**In-place reuse.** The machine decides at run time: `Unpack`, `DropReuse` and
`CtorReuse` each check uniqueness, and a shared cell is copied and left alone. So
`code.rs`'s bookkeeping (stale `known` entries, a token claimed on one path and not
another, a wrong `MOVE`) can lose reuse or read `Erased`, but never change a shared value.
Native code mirrors this: its `operand` erases a register it moves from, so a wrong
`MOVE` reads `Erased` there too, and `Const` clones pool constants (`clone_from`), so a
pool cell or array is never unique and never reused. Tokens are scoped like temporaries
(restored after each arm and branch), so a token register is never reused while still
claimable. Effect `field` and `pair` take fields apart only when unique. I didn't redo
the plan in `docs/research/in-place-reuse.md` or its fresh-eyes review; nothing here
contradicts them.

**Arrays (SW-1637).** `unshared` changes the buffer only under `Rc::get_mut`, and
otherwise copies it and counts the copy. `set` past the end copies nothing. The
by-reference `eval` path clones, so it always copies. The machine's consuming path and
`enter`'s native branch move their operands. Constants and the global cache hold a
reference, so a constant array is never changed in place. `a_shared_array_is_copied_not_changed`
is the soundness test. Version arrays are the JS backend's (`docs/proposals/arrays.md`
§4.3). Nothing in `rt` implements them.

**Freeing.** Work lists for `Fields`, `Fun`, `Delay`, `Resume`, `StateRun`, `Handler`
and `Capture`; the only gap is F2.

**Limits.** Every frame entry and tail call is a step; `charge` saturates; the machine's
frame limit is checked at every push; the runner bounds its own frames
(`run.rs:597-606`); the codec bounds nesting (2,000) and frame size (2²⁰).

**Determinism.** `stitchwort_core::collections::HashMap` uses a fixed hasher. The one
address-keyed table, `code.rs`'s `Uses`, is lookup-only and never iterated. No pass
iterates a map to produce output.

**Numbers.** Total division matches its commit (`f6514d948`): `x / 0 = 0` and
`x % 0 = x` on `Nat` (`div_fuel`) and every `Int` division, small paths falling back to
the big ones on `None`. `IntModNat` of a negative by 0 gives `toNat x = 0`, as commented.

**Agreement.** Machine and native code run the same `Image` and share `prims`,
`effect::state_handler` and `handler_for`, `num_switch` and the frame and step rules.
The places they could drift are F1 and F8. `tests/it/interp` is an independent IR
interpreter for lowering. The core reference evaluator counts steps differently by
design, so only results, not step counts, are comparable with it.

**Fingerprints.** See below. The codec's `BUILD_HASH` covers `rt`'s whole crate graph
from the manifests (`rt/build.rs`).

## The 1 Nov review's findings in this scope

| 1 Nov finding | Status |
|---|---|
| §1.1 Native layout probe reads padding | **Fixed** (`228a6e144`, SW-1122): field-by-field reads, a compile-time check in test builds, a Miri-ready probe test. |
| §1.2 Test fingerprint omits the fast runtime | **Fixed** (SW-1123, then SW-1329): the test cache key is `evaluation_fingerprint` over `core`, `rt`, `dev-features`, `test_run.rs` and the manifests, read from the crate graph. `the_evaluation_fingerprint_covers_core_and_rt_graphs` and `…_changes_with_what_evaluates_tests` test the inputs, not just the hash. `syntax` is excluded on purpose: `rt` uses it only for `Diagnostic` and `Span`. |
| §1.3 Native code lifetimes not enforced | **Fixed for lifetimes** (`4aa28eaa9`, SW-1124; `5e4e54608`, SW-1157). **Still open:** program and image agree by convention (F3). |
| §3 Representations publicly constructible (program vs image, code vs tables) | **Partly open:** code vs tables is fixed by `Crossing::new`; program vs image is F3. |
| §4.2 Unwinding at the JIT boundary | **Addressed:** helpers abort (`internal()`, or `extern "C"`'s no-unwind), and the policy is written at `internal()`. |
| §4.3 Reliance on `Rc`'s private layout | **Unchanged by design:** checked at start-up by `probe_layout`, with a test hook for failure (`STITCHWORT_TEST_LAYOUT_PROBE_FAILS`). |
| §4.3 macOS JIT write-protect state in a `Send` object | Not in `rt` (`crates/native`'s JIT provider); out of scope here. |

## Tickets to file

Grouped into lanes of 30 to 90 minutes.

1. **Native `Array.replicate` cost** (F1). Sonnet, 45-60 min. A `sw_charge` helper, its
   call in `n1` before a replicate `Prim`, the same check in `sw_apply_prepare`, and an
   agreement test of step counts and of a huge count stopping with `Work` on both
   runners.
2. **Arrays freed without recursion** (F2). Sonnet, 30-45 min. A `repr(transparent)`
   `Items` newtype with a work-list `Drop`, and a two-million-deep nested-array test. It
   touches every `Value::Array` match; `probe_layout` should still pass unchanged.
3. **One way to make an `Image`** (F3). Opus, 60-90 min (unsafe boundary). Private
   `Image` and `Code` fields with accessors, a `Compiled` value that `n1::compile`,
   `TableStore::new` and `Outline::of` take, and the call sites in `crates/native`,
   `crates/standalone` and the CLI.
4. **Small runtime fixes** (F7, F9, F10). DeepSeek, 30-45 min. The profiler's fallback
   to sampling every entry; `debug_assert!`s of uniqueness in `sw_empty_cell` and
   `sw_free_emptied`; `assert!` in `prims::fill`; the validator rejecting a field bound
   twice, with a codec test. Each change has its own test.
5. **Nesting guard for `code.rs` and `validate`** (F5). Sonnet, 45 min. A depth check (or
   an explicit stack), and a 50,000-deep `let` chain test on a small thread.
6. **Shared reuse helpers** (F8). Sonnet, 60 min, after lane 2 (both touch `value.rs`).
   `reuse::{unpack, drop_reuse, ctor_reuse}`, one `unique`, one `function_value`, used
   by the machine and `native_abi`. The `alloc_trace` agreement tests guard it.
7. **Text size in the counterexample search** (F4). Sonnet, 45 min, after D2660. Charge
   `TextAppend` and `TextJoin` by result size in `number_words` mode, before allocating,
   at both machine charge sites, with a search test of a doubling text.
8. **Over-application chains** (F6, F11, F12). Sonnet, 45-60 min, after D2661. Count
   nested `Ret`s as frames, an iterative `Frame` drop, the copy note returned rather than
   printed, and the profiler's on-stack counts.

## Questions for Matt

- **D2660: should a run be able to fail for using too much memory, rather than abort?**
  Today steps bound time, and memory only indirectly: `Array.replicate` and big numbers
  (in the search) are charged by size, but a text can double every step (F4), and an
  allocation failure aborts the process. Options: (a) charge size-growing text natives
  in the counterexample search only, as SW-907 did for numbers; (b) charge them
  everywhere; (c) add a byte budget as a new `ResourceError`. **[rec: (a) now, since
  the search is where random sizes come from; (c) only if a real program needs it]**
- **D2661: should a pending over-application count as a frame?** On the machine, a
  function that over-applies itself in tail position builds a chain of pending
  applications that the frame limit doesn't see (F6), so it fails with `Work` (after up
  to 10¹⁰ steps) where the reference evaluator fails with `Depth`. Counting each nested
  continuation as a frame makes the two agree, and changes only which limit such a
  program hits. **[rec: yes]**
