# Code review: `crates/js` and `crates/native` (SW-1900)

Read on `lane/SW-1900` at `c2d5d5aec`, 7 Nov 2026. **Reading only: nothing was built or
run.** Scope: the JavaScript backend (`js/src/lib.rs`, `fast.rs`, `effect.rs`, `run.rs`,
`sourcemap.rs`, about 9.1k lines) and the native code generator (`native/src/n1.rs`,
`n1/runtime.rs`, `aot.rs`, `frames.rs`, `map_jit.rs`, `spike.rs`, `checks.rs`, about
6.6k lines), with every `unsafe` block in `crates/native`. Where a question crosses
into `crates/rt` (the ABI helpers, the natives' binding, the machine's prims) or
`crates/core` (the float rules), I read only what the answer needed, and say so. I
started from the `rt` review (`docs/reviews/code-review-rt.md`) and don't repeat its
findings, except to refine F1 and F3 as asked.

## Summary

Both backends are carefully built, and their agreement with the machine is mostly
designed in rather than hoped for. On the native side, the generator does no
unsafe work of its own: its only `unsafe` blocks build the crossing and cast
trampoline pointers, and both rest on contracts that are written down. Every
index it takes from the image (registers, jump tables, the constant pool, number
tables) is checked by Rust indexing while it compiles. So a bad index panics the
compiler and can't become bad code. The generated code mirrors the machine's
moves, clones, drops, step counts and error-exit order, and a good set of
agreement and allocation-trace tests holds it to that. On the JS side, the number
and text natives match the machine's rules case by case. That includes total
division, Euclidean and floored `Int` division, JS's `Math.round` and `String(x)`
(which `core` copies for the machine), and Unicode scalar order for text. The
version arrays from SW-1638 are a correct Baker reroot, with good tests.

What remains is mostly at the edges:

- `Array.replicate`'s cost on the two other runners. The `rt` review's F1 is
  confirmed, but its suggested fix can't work as written, because native code keeps
  the step count in a register.
- What native code trusts, beyond F3's program/image pairing: value shapes and
  arities.
- A third family of natives bound by name: the effect runtime's four, on every
  backend.
- One likely wrong-answer path in JS, a projection out of an `Array`.
- A few quadratic code generators.

**Top five recommendations**

1. **Charge `Array.replicate` natively, inline from the step register (N1).** The
   steps live in Cranelift's pinned register while native code runs, so a helper
   that adds to `Context::steps` (the `rt` review's `sw_charge`) charges a stale
   counter. Subtract the count in generated code before the `Prim`, and add an
   arrays agreement test to `crates/native`. None exists today (N10).
2. **Close native compilation's trust boundary in one design (N2, D2711).** F3's
   `Compiled` token is necessary but not enough. Native code also trusts the
   program's arities (`sw_apply_cached` picks the direct call by the program's
   arity, while the code's arity comes from the image), and the run-time shape of
   every value it reads a field of. `aot::compile_object` adds a third separate
   piece, the encoded tables.
3. **Pin the effect natives by content hash, and refuse loudly as arrays do (N3,
   D2710).** `bind`, `foldComp`, `translate` and `runPure` are replaced on the
   machine, natively and in JS by registry name and arity alone. If their shape
   changes, JS falls back to the library code silently. This is the same gap as
   `core`'s F2 (D2640).
4. **Compile `Term::Proj` in JS through the same path as a match (N4).** As it is,
   `Proj` on the library's `Array` emits `(x).toList`, which is `undefined` on a
   version array, while the machine lowers every projection as a match
   (`lower.rs:615`).
5. **Bound the quadratic generators (N5, N6).** In native code, each call's
   error exits spill every live register: O(calls × live) code per body. In JS, a
   whole-body scan runs per `let` and per text or array match, and the tail-loop
   search regenerates a body up to six times.

**Findings by severity:** high 0, medium 4, low 9.

## Findings

| # | Where | What | Sev | Conf | Size |
|---|---|---|---|---|---|
| N1 | `n1.rs:3881`, `:3896` (`prim_owned`, `prim`); `:1462` (`steps_out`); `js/lib.rs:5538` | `rt` F1 confirmed and refined: native code can't charge `Array.replicate` through the context; JS doesn't count and allocates `new Array(Number(count))` | medium | high | M |
| N2 | `n1.rs:786-797` (adapters), `:3335` (`Field`), `:3241` (`Captured`), `:4018` (`unpack`); `native_abi.rs:1793`; `aot.rs:75` | `rt` F3 refined: besides the image, native code trusts the program's arities and every value's shape; AOT adds the encoded tables as a third separate input | medium | medium | L (D2711) |
| N3 | `rt/effect.rs:136`, `js/effect.rs:94-110`; `js/lib.rs:2349-2354`, `:5323-5338` | The effect natives and JS's rewrites of `ifThenElse`, `Decidable.elim`, `Ord.compare`, `List.append`, `Nat.add` are bound by name and shape only | medium | medium | M (D2710) |
| N4 | `js/lib.rs:4159-4171` | `Term::Proj` on `Array` emits `(x).toList`, which is `undefined` on a version array; special representations are hand-listed in four places | medium | low | S |
| N5 | `n1.rs:2813` (`exit_now`), `:2928`, `:2891`, `:2909`; `:2356` (`maybe_full`) | Every call site has up to three error exits, each spilling every live register: code is O(calls × live); the analysis is O(instrs × regs) bits | low | medium | M |
| N6 | `js/lib.rs:3924`/`5700` (`single_use`), `:3093`, `:3107` (`mentions` on output), `:2840-2870` (six tries), `:2889-2930` (member inlining) | JS generation is quadratic in `let` chains and nested text or array matches, and can multiply inlined members along a chain | low | medium | M |
| N7 | `js/lib.rs:2797-2815`, `:4193`, `:4196`, `:2562` | A `@[tailrec]` the JS backend can't loop, or a malformed term, panics the compiler instead of giving a diagnostic | low | high | S |
| N8 | `map_jit.rs:136-157` | The `MAP_JIT` write permission is per thread, but each provider tracks it on its own: two modules compiling on one thread can make each other's memory non-writable | low | medium | S |
| N9 | `n1.rs:2024` (`inc_f`) | Under `trace_refcounts`, `Text.fold` still increments `f` inline, so the trace misses that count | low | medium | S |
| N10 | `crates/native/tests/it/*` | No native test touches arrays (in-place `prim_owned`, `replicate`, traces); it would have caught N1 | low | high | S |
| N11 | `js/lib.rs` (6,566 lines) | 1 Nov §4.4 still open and growing: boundary planning, codecs, runtime strings, natives and emission in one file | low | high | M |
| N12 | `js/lib.rs:5539` | `new Array(n).fill(x)` makes a holey array: slower element reads for the array's life in V8 | low | medium | S |
| N13 | `n1.rs:1461`, `:1486`, `:1545`; `fast.rs:10`; `n1.rs:183-191` | Stale comments: the machine running bodies for native code (gone since NO4), `MAX_WORK` (doesn't exist), "N of the N bodies" | low | high | S |

## Details

### N1. `Array.replicate`'s cost on native code and in JS (medium, high)

The `rt` review's F1 is right: nothing in `crates/native` mentions `replicate`.
`Gen::prim_owned` (`n1.rs:3881`) and `Gen::prim` (`:3896`) call `sw_prim_owned` or
`sw_prim` directly, and the machine charges `prims::replicate_cost` first
(`machine.rs:576`, `:1184`).

**The refinement: F1's fix can't work as written.** While native code runs, the
steps left live in Cranelift's pinned register (module comment, "Counting";
`count_step_with`, `n1.rs:2891`). The context's `steps` is written only around
`sw_apply_prepare`, by `steps_out` and `steps_in` (`:1462`, `:1473`, used at `:1541`
and `:1653` only). A helper `sw_charge(context, cost)` called from a `Prim` site
would add to a stale count, and the next `steps_in` doesn't happen there, so the
charge would be lost or overwritten. Two ways that work:

- **Inline (preferred):** before a `Replicate` `Prim`, load the count register. If
  it is a small `Nat` no greater than the pinned value, subtract it. Otherwise
  leave through the out-of-steps exit (`exit_with` with `OUT_OF_STEPS`, which
  already sets the register to "one over"). A big `Nat` count is out of steps,
  as `replicate_cost` makes it `u64::MAX`.
- Or bracket that one helper call with `steps_out` and `steps_in`, and let
  `sw_prim` charge the context.

In `sw_apply_prepare`'s function-value path, the context *is* current, so the
`rt` side of F1's fix (the check in `sw_apply_prepare`) stands as written.

**JS.** JS doesn't count steps at all (`run.rs:20-21`: "JS has no tick limit"), so
here the problem is memory, not agreement. `Array.replicate` is
`arrayOfItems(new Array(Number(count)).fill(x))` (`lib.rs:5538`). A count of 2³² or
more throws `RangeError`, which `outOfResources` turns into a
`StitchwortResourceError`, so that case is fine. A count of a few hundred million is
accepted and then exhausts the heap. That is a fatal, uncatchable out-of-memory in
V8: under `run --js` the worker reports `ERR_WORKER_OUT_OF_MEMORY` (handled by the
launcher), but in a `build --js` library it takes down the host page or process.
Under the machine's step limit, the same count stops with `Work`. Refusing counts
above some bound with a `StitchwortResourceError` would be a small, honest fix. The
bound is an implementation choice.

**Fix (M, Sonnet; after or with `rt` F1's lane):** the inline charge in `Gen::prim` and
`Gen::prim_owned` for `PrimOp::Array(ArrayNative::Replicate)`, the `sw_apply_prepare`
charge from F1, and N10's tests. Assert that the step counts agree with the machine,
and that a count of 10¹² stops with `Work` natively. JS's bound can go in the same
lane.

### N2. What native code trusts (medium, medium; D2711)

F3 says the generated code "indexes frame slots, jump tables and `Tables` by the
image's numbers", and that an out-of-range one is undefined behaviour. Reading `n1`
changes that picture:

- **Image indices are checked while compiling.** Registers are Cranelift variables
  indexed with `self.vars[r]`. Jump tables are read with `code.tables[table]`, the
  pool with `self.image.pool[k]` (`n1.rs:3161`), number tables with
  `code.num_tables[table]`, and callees with `self.functions[&callee]` and
  `image.global_code[g]`. Every one is safe Rust indexing at compile time, so an
  out-of-range number panics the compiler. The pool and caches that generated code
  reads at run time come from the same image (`TableStore::new(program, &image,
  n_caches)`, `n1.rs:458`), so their offsets agree. A tag outside a `Switch` table
  reaches the `trap` block (`:3114`), a crash but not UB.
- **What is trusted is the program, and the shape of values:**
  - *Arities.* Each global's adapter `value{g}` is declared with the **program's**
    `params` (`:786-797`) and defined with the **image's** `code.params`.
    `sw_apply_cached` (`native_abi.rs:1793`) takes an `Apply` site's direct path
    when the **program's** arity equals the site's argument count. It then calls
    `functions[g]` through `value_sig(n)`. If program and code disagree, that
    indirect call passes the wrong number of words: undefined behaviour that
    Cranelift's verifier can't see (it's indirect).
  - *Shapes.* `Field` (`:3335`) loads field `i` at `RC_VALUE_AT + 24·i` from
    whatever the register's second word points at. `Captured` (`:3241`) does the
    same for a closure's captures, and `Unpack` (`:4018`) for each field it binds.
    Nothing checks that the register holds a `Data` of at least `i + 1` fields, or
    a closure with that many captures. The machine panics on the same input
    (`machine.rs:1356-1360`, `fields[i as usize]`). `Program::validate` checks
    structure, not run-time types, so even a private-fields `Image` made by
    `code::compile` from an ill-typed program that passes `validate` gives code that
    reads out of bounds.
  - *The object file.* `aot::compile_object(program, image, tables, …)` (`aot.rs:75`)
    takes the encoded tables as a separate `&[u8]`, encoded by the caller. Code
    compiled for one image with another image's pool is the same problem, carried
    into an executable.

Today the only callers lower the program in-process just before (`cli/main.rs:2990-3001`
and the build path), so nothing here is an observed bug. But an API whose safe
functions can produce out-of-bounds reads needs either an `unsafe` contract or a
type that proves the inputs. D2711 asks which.

**Recommendation (L: a short design note first, Opus):** extend F3's `Compiled` value
so that it carries the program, the image and (for AOT) the encoded tables, made by
one function from a program lowered in-process, and make `n1::compile`,
`aot::compile_object`, `TableStore::new` and `Outline::of` take only it. If decoded
programs should ever compile natively, add a run-time-shape validator first (D2711).
Either way, add a debug-build check in `sw_apply_cached` that the program's arity
equals the code's, a single compare.

### N3. Natives and rewrites bound by name (medium, medium; D2710)

The `core` review (F2, D2640) found the kernel's Nat natives bound by type shape
only. Text, `Int`, `Float` and `Array` natives are bound by content hash on every
backend (`rt/natives.rs`), and arrays refuse loudly when stale (`E-BUILTIN`). The
pattern doesn't reach these:

- **The effect runtime's four.** `Effect.bind`, `foldComp`, `translate` and
  `runPure` are replaced on the machine (and so natively) by `EffectNatives::new`
  (`rt/effect.rs:136`), and in JS by `Effect::new` (`js/effect.rs:94-110`). Both
  check only that the registry has a definition of that name with the right number
  of run-time parameters, and that `Comp` has two constructors with the expected
  field counts. Suppose someone edits `bind`'s body in `std` and keeps its type: all
  three runners keep running the old semantics, and nothing fails until a
  differential test notices. Suppose instead the shape changes: both quietly fall
  back to the library definitions, which is a performance cliff with no message,
  unlike arrays. The two checks also differ: `rt` also refuses an unboxed `Comp`,
  and JS doesn't.
- **JS's semantic rewrites.** `Gen::new` (`js/lib.rs:2349-2354`) takes
  `Bool.ifThenElse`, `Decidable.elim`, `Ord.compare`, `Ord.fromCompare`,
  `List.append` and `Nat.add` from the registry by name. The generator then
  assumes what they mean:
  - `if_then_else` becomes a JS conditional with the literal tag `"True"`
    (`:4352-4358`);
  - `List.append`'s second argument is the hole of a TRMC loop (`:3387`);
  - `Nat.add` drives calls "modulo addition";
  - `known_compare` reads `Ord.fromCompare`'s body.
- **Hard-coded constructor names.** `native_js` returns `{ tag: "Yes" }` for
  `DecEqNat` and `{ tag: "True" }` for `Leq` (`:5323-5338`), while
  `decision_yes_tag()` reads the real name from the registry. The hash-bound
  natives are safe here, since a renamed `Option` changes `Text.uncons`'s hash. The
  Nat natives aren't.

**Recommendation (M, Opus, in D2640's lane if Matt agrees):** a hash table for the
four effect natives as for arrays, shared by `rt` and `js` (one `bind_effects` in
`rt/natives.rs`), with the all-or-nothing loud refusal. For the JS rewrites, pin each
definition the generator reasons about to a hash (or derive the rewrite from the
definition's body, as `known_compare` already half does). Take tags from the
registry everywhere.

### N4. A projection out of an `Array` in JS (medium, low)

`Term::Proj(d, i, t)` (`js/lib.rs:4159-4171`) handles three cases: an erased field,
`Float`, and a record stored unboxed. Anything else reads the property:
`(x).toList`. The library's `Array` is a one-field record, but `Gen::unboxed`
excludes it on purpose (`:2485`), because inside generated code an array is a
version array `{ items, op, index, value, next }`. So `Proj(Array, 0, a)` compiles to
`(a).toList`, which is `undefined`. The `match` path handles `Array` (`:3097-3110`,
`listOfArray`), and the machine lowers every projection *as* a match
(`rt/lower.rs:615`, `Term::proj_as_match`). The two backends would disagree there.

Whether a `Proj` on an array reaches the JS generator is the open question, hence the
low confidence. Field syntax elaborates to the projection function, which the
`ToList` native replaces. But `Term::Proj` is produced by quotation
(`core/reference.rs:569`) and by the unifier's solutions (`elab/unify.rs:2307`,
`:2397`), and the generator imports `eval`, `quote` and `expand_step`. Check `Text`
the same way, if it's a record: `MkText`'s field is matched with `charsOfText` at
`:3083-3096`, but has no `Proj` branch.

There is a pattern here: the special representations (`Nat`, `Int`, `Text`, `Float`,
`Array`, unboxed records) are listed by hand in at least four places (`unboxed`
`:2484`, `is_identity_match` `:3131`, the cell test at `:3545`, `Proj`), and each new
representation has to remember all of them.

**Fix (S, Sonnet):** compile `Proj` as `rt` does, through the case path
(`Term::proj_as_match`), so it inherits every representation's match. Add a
regression test that builds a `Proj` on an array term directly, plus one through a
quoted solution if one can be found.

### N5. Native error exits are O(calls × live) (low, medium)

Each `Call` or `Apply` site has up to three exits: steps (`count_step_with`, `:2891`),
frames (`push_frame_with`, `:2909`) and the callee's error (`call_result`, `:2928`).
`exit_now` (`:2813`) spills every register that may hold a value at that point, three
stores each, and calls `sw_unwind`. A body that builds a large constructor or list
from computed parts holds k live values across k calls, which gives about 3k² spill
sequences. The analysis behind it, `maybe_full` (`:2356`), keeps a bit set of all
registers per instruction: O(instrs × regs / 64) words, iterated to a fixed point.
A 50,000-instruction body with 50,000 registers (a long pure `let` chain, if `code.rs`
gives each binder its own register; I didn't check) needs about 300 MB for it. The
wide frames this makes are refused cleanly by `stack_for`, so the failure is a slow
compile or a big binary, not a crash. That is why the severity is low.

**Fix (M, Sonnet; measure first):** count a census of `released × exits` per body on
the AoC programs. If it matters, share one exit block per distinct live set (block
parameters for the values), or spill live values to a fixed frame area on entry to
a cold exit and call one helper with a bitmap. Make `maybe_full` sparse for bodies
with more than a few thousand registers.

### N6. Quadratic scans in JS generation (low, medium)

- `single_use` (`:5700`), called for each `let` (`:3924`), walks the rest of the body
  until it finds a second use. In a chain of n lets whose variables are used once,
  near the end, that is O(n²) term visits.
- For each `Text` or `Array` match, `mentions(&body, &var(level))` (`:3093`, `:3107`)
  scans the generated JS text of the whole branch, which makes nested matches
  O(size × depth). It is also fragile: a string literal containing `v3` counts as a
  use (harmless here, only extra work).
- `self_tail_loop` (`:2840-2870`) regenerates the case tree for up to six
  configurations, and member inlining (`inlines_member`, `:2889-2930`) inlines along
  chains. `call.inlined` is a stack (`:3763-3765`), so a group of k members that each
  call the others at s sites can inline s^k copies.

The generator checks its stack at every level (`budget.nesting`), so none of these
can crash it. They can only make it slow.

**Fix (M, Sonnet):** one use-count pass per body (a vector by level) in place of
`single_use` and `mentions`, and a size budget on inlining (stop inlining once the
loop body passes some multiple of the definition's own size, and fall back to the
next configuration). Test with a 20,000-let chain under a time bound.

### N7. Generator panics instead of diagnostics (low, high)

`tailrec_not_looped` (`:2797-2815`) panics when a `@[tailrec]` definition didn't
become a loop. tailrec.md asks for an assertion, but the elaborator's tail-recursion
check and the JS backend's loop-building are separate analyses, so a definition the
checker accepts and JS can't loop crashes `build --js` and `run --js`. The same goes
for `case outside a case tree` (`:4193`), an unsolved metavariable (`:4196`) and `no
info for` (`:2562`). The driver's worker pool catches panics (`driver.rs:129`), but
the CLI's direct JS paths and the playground show a crash. **Fix (S, DeepSeek):**
return an `E-INTERNAL` diagnostic naming the definition, keep the panic under
`cfg(debug_assertions)` so tests still fail loudly, and add a test that forces the
path.

### N8. `MAP_JIT` write permission across two providers on one thread (low, medium)

The 1 Nov review's §4.3 concern is addressed (SW-1124). `set_writing` panics when a
provider made writable on one thread is used on another, and `Drop` restores the
thread's protection when it runs on the writer. One gap remains:
`pthread_jit_write_protect_np` is a per-thread switch, but `writing` is per
provider. Suppose providers A and B are both writing on one thread (two
`JITModule`s compiling interleaved, or one dropped mid-compile while another is
open). B's `finalize` then makes the thread's `MAP_JIT` memory executable, and A's
next write faults (`SIGBUS`). Nothing does this today, since the CLI compiles one
module at a time and tests compile on separate threads, and the outcome is a crash,
not silent corruption. **Fix (S, Sonnet):** a `thread_local!` count of writers, so
that protection is restored only when it reaches 0.

### N9. Trace mode misses one count (low, medium)

`emit_text_fold`'s `inc_f` (`n1.rs:2024`) increments `f`'s strong count inline, even
under `Options::trace_refcounts`. Every other clone uses `helpers.inc` there. So a
traced `Text.fold` run has one increment per character that the trace doesn't record.
That only matters if the trace compares increments, and the agreement tests
(`text_fold_error_exits_make_the_machines_allocation_trace`) pass, which suggests it
records allocations and frees only. **Fix (S, DeepSeek):** route `inc_f` through
`helpers.inc` under the trace, or say in `Options`' doc which counts the trace sees.

### N10. No native array tests (low, high)

`crates/native/tests/it` has agreement and trace tests for numbers, text, closures,
handlers, delays and tail calls, but none mention arrays. `rt`'s `tests/it/arrays.rs`
runs only the machine. The native code path for arrays is its own:
`prim_owned` moves operands so that an unshared array changes in place, and
`replicate` is N1. **Fix (S, Sonnet, in N1's lane):** add `arrays_agree` (results and
steps, on the machine and natively), an allocation-trace test that shows in-place
`set` and `push` on an unshared array and a copy on a shared one, and the huge
`replicate` count.

### N11. `js/lib.rs` keeps growing (low, high)

The 1 Nov review (§4.4) counted 6,280 lines in this file, mixing boundary planning,
codecs, runtime strings and emission. It is now 6,566. `fast.rs`, `effect.rs`,
`run.rs` and `sourcemap.rs` are already separate, so the split has started. **Fix (M,
DeepSeek, mechanical):** move it out in three parts with no behaviour change, checked
by the JS snapshots:
- the boundary (`Boundary`, `exportable`, `check_codec`, `field_boundaries`,
  `input_datas`);
- the runtime's JS strings (`RUNTIME`, codecs, `VERSION_ARRAYS`, `FLOAT_BITS`);
- the natives' JS (`native_js`, `float_native_js`, `int_native_js`,
  `array_native_js`, `text_native_js`).

That leaves `Gen` in `lib.rs`.

### N12. `Array.replicate` makes a holey array in JS (low, medium)

`new Array(n)` creates a holey backing store, and `fill` doesn't change V8's
elements kind back to packed. So every later read of that array (and its versions,
which share the buffer) takes the holey path. Day-15-style code that starts from
`Array.replicate` pays this throughout. **Fix (S, DeepSeek):** fill a `[]` with a
`push` loop (or `Array.from({ length: n }, () => x)`). Measure on the
`a_hundred_thousand_array_sets_run_quickly` program.

### N13. Stale comments (low, high)

- `n1.rs:1545` says "A failure in `sw_apply_prepare` (in the machine, for a body
  that isn't compiled)".
- `:1486` mentions "what the machine computed for a function value without native
  code", and `steps_out` (`:1461`) says "for a helper that runs the machine".

Since NO4 and NO5, the machine runs nothing for native code (the module comment
says so). `fast.rs:10` describes a `MAX_WORK` limit that doesn't exist anywhere.
`Islands::note` (`:183-191`) prints "running N of the N bodies", a leftover of
partial compilation. **Fix (S, DeepSeek)**, per CLAUDE.md's comment rules.

## Checked and sound

**Unsafe code in `crates/native`.**
- `n1::compile`'s `Crossing::new` (`:466`) satisfies its contract. The module
  (whose code is never unmapped) and the image are owned by `Islands`, with
  `crossing` declared first.
- `trampoline` (`:1334`) asserts that the size matches and is used only on the
  three trampolines `emit` made with those signatures.
- `map_jit.rs`: `mmap` with `MAP_JIT` and a checked failure; bounds-checked chunk
  arithmetic in `allocate_code`; `sys_icache_invalidate` only on ranges it handed
  out; `free_memory` forwarded; `Send` justified (residual: N8).
- `spike.rs`: the context pointer and the two `transmute`s are dev-only, with
  their contracts stated.

**Generated code's layout assumptions.**
- Words: tag byte 0, a constructor's tag at bytes 4-7, payload at 8, length at 16.
- An `Rc`'s strong count at 0, weak count at 8, value at 16.
- `FUN_KEY_MASK` drops the padding bytes, so native code reads them but never
  depends on them. The variant byte keeps a `Pap` from ever matching a cache key.
- All of this is checked at start-up by `probe_layout` (`preflight`, and again in
  the executable).

The inline reference counts match `Rc`'s:
- `unique` tests `strong == 1 && weak == 1`, since the stored weak count includes
  the implicit one.
- A drop decrements inline only when `strong > 1`, and lets `sw_drop_words` free
  otherwise.
- A clone increments without the overflow check that `Rc::clone` has. That is
  sound in practice: 2⁶⁴ live references can't exist.

On reuse:
- `CtorReuse` writes into a token cell without dropping, which is right, because
  every token comes from `Unpack` (fields moved out or erased by `sw_empty_cell`)
  or `DropReuse`.
- The fast path checks the token is `Data` of the same length and unique.
- `Unpack`'s "free without walking" happens only when every field was taken once.

**Agreement on numbers and text (JS against the machine).**
- *Nat:* truncated subtraction, total `divFuel`, and native code's inline small
  paths (overflow falls back to the helper; a divisor of 0 gives 0 without the
  trapping division).
- *Int:* Euclidean (`div`/`mod`), truncated (`tdiv`/`tmod`) and floored
  (`fdiv`/`fmod`) division by 0 as total division says, and `modNat` by 0 as
  `toNat`. `Text.toInt` and `Text.toNat` accept exactly ASCII digits.
- *Float:* `round` is JS's, and the machine uses `core::float::js_round`.
  `toText` is `String(x)` against `js_to_string`, and `ofNat` is `Number(bigint)`
  against `nat_to_f64` (round to nearest, ties to even, and infinity past 2¹⁰²⁴).
  `compare`, `<=` and `<` are the total order with NaN greatest and `-0 < 0`. Bit
  conversion is confined to one module.
- *Text:* length, `take`, `drop`, `uncons` and `fold` work by scalar value.
  `compare` is scalar order, by the argument in its comment. `trim` uses Unicode
  `White_Space`, not JS's `trim`.
- *Well-formedness:* every native that builds a string from well-formed strings
  keeps it well-formed, so `scalarEndingAt`'s assumption holds.

**JS version arrays (SW-1638).**
- `reroot` undoes each kind of change correctly (set, pop and push invert to set,
  push and pop), in a loop.
- `arrayChanged` makes the old version a change to the new one.
- Set past the end returns the same version. Push on an empty array is fresh, so
  `Array.empty` isn't turned into a change.
- Decoding builds a fresh buffer. Encoding copies the elements first (`.slice()`),
  because encoding one can reroot.
- Two references to one decoded input share a version, which is safe because
  versions are persistent.
- The tests cover old versions read after newer changes and 100,000 sets.

**JS boundary.**
- The fast codecs only accept or give up, and fall back to the general decoder
  with the counters saved and restored, so re-entrant exports from getters are
  safe.
- `MAX_DEPTH` hands deep input to the loop decoder.
- `__proto__` keys are computed.
- `SafeNat` and `SafeInt` check the bounds and wholeness and read `-0` as 0.

**Effect runtime in JS.** `effPending` is a global, but every reader takes it
immediately after the `effRun` that set it, so nested runs can't interleave. Pending
continuations are a persistent list, so resumptions can be reused. Lazy folds keep
`bind` chains off the JS stack.

**Recursion and limits.**
- The JS generator checks its stack at every level (`budget.nesting`), and
  `dependency_order` is iterative.
- Generated JS loops only self tail calls (with calls modulo constructors and
  addition, and inlined group members), as tailrec.md says. Other recursion uses
  JS frames: `run --js` gives the worker a 2 GB stack, and `build --js` maps stack
  overflow to `StitchwortResourceError`.
- Native frames:
  - The frame bound is read from the prologue, with an IR-based fallback, plus
    stack-argument growth from tail calls.
  - The stack-pointer backstop at every counted call (and in `rt_text_fold`) makes
    a wrong bound fail as `E-RESOURCE`, never as an overflow.
  - Frames of a page or more are probed.

**Determinism.** Every map in both crates is `stitchwort_core::collections`' (fixed
hasher). No output depends on iteration order: the module text is appended in
order, and the source map numbers files and names by first appearance.

**Source maps** (`sourcemap.rs`, D940-D945).
- VLQ encoding is tested against the specification, and relative fields reset as
  version 3 requires.
- Columns are UTF-16 code units on the source side. On the generated side they are
  ASCII positions, since `$` follows `const ` and names are encoded.
- `name_offset` prefers `def name` within the span and takes a whole word only.
- The runtime glue stays unmapped. `run --js` has no map yet (stage 3, by design).

**Audit (S4).** In debug builds every `iconst` is checked against host addresses,
and `listing` keeps IR text that doesn't depend on where the program is. That is
what makes the AOT object relocatable.

## The 1 Nov review's findings in this scope

| 1 Nov finding | Status |
|---|---|
| §1.3 Native code lifetimes not enforced (`n1::compile` borrowing the image) | **Fixed** (SW-1124): `compile` takes the `Image` by value, with a `compile_fail` doctest (`n1.rs:429-435`). Program/image agreement is still open: `rt` F3, refined here as N2. |
| §3 Representations publicly constructible (program vs image) | **Open**, and wider than stated: arities and value shapes (N2), and AOT's separate tables. |
| §4.2 Unwinding at the JIT boundary | Not in this crate's code: helpers are `rt`'s (see the `rt` review). Generated code stops at a trap instruction on an internal error rather than unwinding. |
| §4.3 macOS JIT write-protect state in a `Send` object | **Addressed** (SW-1124): the thread is recorded, use from another thread panics, and `Drop` restores protection on the writer. Residual: two providers on one thread (N8). |
| §4.4 `js/lib.rs` at 6,280 lines, mixed responsibilities | **Open**, now 6,566 (N11). |
| §5 Separate backend-neutral representation contracts from target emission | **Partly done:** natives and representations are bound once in `rt::natives` (`Representation`, `bind_array`) and shared. JS still hand-lists the special representations (N4) and binds its rewrites by name (N3). |

## Tickets to file

Grouped into lanes of 30 to 90 minutes.

1. **Native and JS `Array.replicate` cost, with native array tests** (N1, N10, N12).
   Sonnet, 60-90 min, with or after `rt` F1's lane (same helpers). Inline charge from
   the pinned register in `Gen::prim` and `Gen::prim_owned`, the
   `sw_apply_prepare` charge, `arrays_agree` and trace tests in `crates/native`,
   and JS's count bound and packed fill.
2. **Native trust boundary: design note** (N2, with `rt` F3). Opus, 60 min, a note in
   `docs/proposals/`. Covers a `Compiled` token carrying the program, image and
   encoded tables; who may make one; and whether decoded programs ever compile
   natively (D2711). The implementation lane follows the decisions.
3. **Effect natives pinned by hash, shared by `rt` and `js`** (N3). Opus, 60-90 min,
   with D2640's lane if Matt agrees (D2710). One `bind_effects` in `rt/natives.rs`
   with a loud refusal; JS's rewrites pinned or derived; tags from the registry.
4. **JS projections through the match path** (N4). Sonnet, 30-45 min. `Proj` as
   `proj_as_match`, regression tests on `Array` (and `Text` if it's a record).
5. **JS generator: panics to diagnostics, stale comments** (N7, N13). DeepSeek, 30
   min.
6. **Quadratic generators** (N5, N6). Sonnet, 60-90 min. Measure first (a census of
   exit sizes on AoC, a 20,000-let JS test), then shared exits and one use-count
   pass.
7. **Small native fixes** (N8, N9). Sonnet, 30 min. A thread-local writer count in
   `map_jit`, and `inc_f` under the trace.
8. **Split `js/lib.rs`** (N11). DeepSeek, 60-90 min, mechanical, after lanes 4 and 5
   (same file). The snapshots guard it.

## Questions for Matt

- **D2710: should the effect runtime's four natives (`bind`, `foldComp`, `translate`,
  `runPure`) be bound by content hash on every backend, with the same loud refusal
  as arrays, rather than by name?** Today, if someone changes one of them in `std`
  and keeps its type, the machine, native code and JS all keep the old behaviour,
  and a change of shape silently drops to the slow library code. [Recommendation:
  yes, in the same lane as D2640 (the Nat natives), since it's the same table and
  test pattern.]
- **D2711: should native compilation accept only programs lowered in the same process
  (enforced by a type that only lowering can make), or also programs decoded from
  bytes?** Native code trusts that a program's arities and value shapes are right.
  The machine checks them (it panics), and native code doesn't (it reads out of
  bounds). [Recommendation: in-process only, enforced by a `Compiled` token, with no
  run-time validator. Nothing compiles decoded programs natively today, and the
  standalone executable embeds tables made at build time.]
