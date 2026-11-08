# Fast paths in native `Apply` for the effect runtime's values (SW-2336)

SW-2336, 8 Nov 2026, Opus. Stage 1 of
[parse-runtime.md](parse-runtime.md) (§2.1, option A), designed from the
code at `4f33434ec` and SW-2335's counts (parse-runtime.md §3.1). Claims
are **[read]** (in the code), **[measured]** or **[estimated]**.

## 1. The problem

In native code, `Apply` of a function value tries the site's one-entry
cache inline (`Gen::apply_target_of`, `crates/native/src/n1.rs`; `Rt::target_of`
in `n1/runtime.rs`). On a miss it calls `sw_apply_cached`
(`crates/rt/src/native_abi.rs`), which fills the cache only for a
`Fun::Global` or `Fun::Closure` taking exactly the site's `n` arguments
and returns 0 for anything else; the site then calls the apply stub
(`apply{n}`, `emit_apply_any`), which calls `sw_apply_prepare` **[read]**.
`sw_apply_prepare` has a fast path for a partial application given exactly
its remaining arguments; everything else collects the arguments into a
`Vec` first **[read]**.

So the effect runtime's own function values (`DoneK`, `JumpK`, `StateK`,
`DelayK`, lazy and eager resumptions, `StateRun`) pay a failed
`sw_apply_cached`, the stub, and a `Vec` allocation and free on every
apply, though each is a leaf that builds one value or is planned as
`RESUME_CODE` **[read]**. The fast-path PAP pays the failed
`sw_apply_cached` too. And `rt_loop`'s continuation site (the `k x` of a
pop) sees every continuation of the program, so its one entry misses on
86–100% of pops, each miss a runtime call **[measured, SW-2335]**.

## 2. The changes, by kind

None changes the native ABI outside `crates/rt` and `crates/native`: the
`Context`, `Tables`, `ApplyPlan` and the stubs' signatures stay as they
are. A site just owns more cache entries.

**A. No `sw_apply_cached` call for a value it can't cache.** In the miss
block of both `apply_target_of` and `target_of`, load the `Fun`'s variant
byte (offset 0 of the `Rc`'s value, as `probe_layout` checks) and call
`sw_apply_cached` only if it is `FUN_GLOBAL` or `FUN_CLOSURE`; otherwise
the target is 0 at once. `sw_apply_cached` has no effect but the cache
write for those two variants, so skipping it for the others changes
nothing observable **[read]**. This covers every leaf, both resumptions,
`StateRun` and every PAP (fast or slow).

**B. The leaves in `sw_apply_prepare`, before the `Vec`.** Beside the PAP
fast path, a match on the bare function value (not a PAP) when `n` is the
value's arity:
- `DoneK` (1), `StateK` (1), `DelayK` (1), lazy `Resume` (1), `JumpK` (2):
  read the arguments from `args`, call the same `effect::done_k`,
  `state_k`, `delay_k`, `resume_lazily`, `jump_k` the general path calls,
  write the value with `code` 0, `arity` 0, `rest` 0, then drop `f`;
- eager `Resume` and `StateRun` (1), only when `Context::resumes`:
  `code` `RESUME_CODE`, `env` `into_word(h.clone())`, the argument moved to
  the plan's first value, `arity` 1, `rest` 0, then drop `f`.

This is exactly the general path's work for these kinds with the `Vec`
taken out: the arguments are moved (no clones in either), the value built
(`resume_lazily` clones the resumption and counts a resume, as before), the
reference for `env` cloned, then `f` dropped last **[read]**. The stub is
unchanged, so it still counts no step or frame for a value plan or for
`RESUME_CODE`, and drops the function value and closure it was given in
the same places. Over-application and the wrong number of arguments keep
the general path. The codegen doesn't change.

**C. A 4-entry cache at the effect runtime's continuation sites.** `rt_loop`'s
pop site (`k x`) and `rt_resume`'s `rest y` sites own four consecutive
`ApplyCache` entries instead of one. A hit compares the key with each
entry in turn and calls that entry's code. A miss (of a global or a
closure, after A) moves entries 0–2 down one, then calls `sw_apply_cached`
on entry 0, which fills it if it can (if not, entry 0 is left as a copy of
entry 1, which is harmless). Which entry holds a key never changes which
code a key calls, so this is as invisible as the one-entry cache **[read]**.
Body sites keep one entry: they are mostly monomorphic. If four entries
still miss most of the time (the site-miss counts say), the fallback is a
lookup with no cache: the variant byte, the lambda's or global's parameter
count from a table, and the code from `Context::lambdas` / `functions`.
That needs a new table pointer, so it is held back.

**D. The general path's `Vec`.** Left for after the counts: once B has
taken the leaves out, what remains is a slow PAP, a native as a function
value, `bind` as a value and wrong-count applications. If those are under
a tenth of the original slow applies, the `Vec` stays (it then costs less
than the risk of reordering the general path's drops).

## 3. What stays identical to the machine

- **Steps and frames.** None of A–C changes which plan is built or how the
  stub or a direct call counts. A cache hit calls exactly the code
  `sw_apply_cached` would have returned; B's plans are the general path's.
- **Clones and drops.** B keeps the general path's order (value built,
  then `f` dropped; then the stub's drops); A and C don't touch values. So
  allocation traces and effect counts stay the same, and the
  `n4.rs`/`n2b.rs` agreement tests and sweeps should pass unchanged.
- **Error exits.** B's kinds can't fail (the general path's internal error
  for an eager resumption without `resumes` stays on the general path). A
  and C run before anything is taken apart.

## 4. Expected effect, and what is measured

Baseline at `4f33434ec` (`task profile:native`, `task bench:compare
--instructions`) **[measured]**:

| | expressions | scan | bridge |
|---|---:|---:|---:|
| instructions | 540 G | 509 G | 143 G |
| `sw_apply_cached` calls | 304.5 M | 292.6 M | 65.9 M |
| of them, returned 0 | 243.6 M | 226.0 M | 47.6 M |
| `sw_apply_prepare` calls | 262.2 M | 248.5 M | 54.2 M |
| of them, the PAP fast path | 100.0 M | 95.0 M | 19.2 M |
| of them, leaves and resumptions (B) | 124.7 M | 108.6 M | 21.4 M |
| of them, a slow PAP or a closure (D) | 37.4 M | 44.9 M | 13.2 M |
| pops; misses at the pop site | 100.7 M; 86.9 M | 73.8 M; 73.8 M | |

`sw_apply_prepare`'s self time is 10.9% of expressions, about 225
instructions a call on average, and `mi_malloc`/`mi_free` another 19%
(the `Vec` is one allocation of many).

- A removes 243.6 M runtime calls on expressions; at about 30
  instructions each, 7 G (1.3%).
- B takes the `Vec`, its free and the general loop off 124.7 M applies; at
  about 250-300 instructions each, 30-37 G (6-7%).
- C saves most of the pop site's resolved misses, at most about 60 M
  calls, 2 G (under 0.5%), if four entries cover the continuations in
  rotation. It is the most code for the least gain, so it goes last and
  only if A and B land as predicted.
- D would take another 37 M applies off the `Vec`, perhaps 7 G (1.3%).

So about 1.08-1.12× on expressions and scan **[estimated]**, not the
1.2-1.3× parse-runtime.md §2.1 guessed from `sw_apply_prepare`'s 23%
inclusive time: most of that is building the values and dropping the
function values, which stay. Bridge and disk gain less.

Measured per stage: the call counts above, and instructions retired for
expressions, scan, bridge and disk. A stage is kept if its counts fall as
predicted and no program's instructions rise.

## 5. Decision

Go ahead with A and B (the lane's call, within Matt's go-ahead): no
step, frame, result or trace changes, no ABI change outside the two
crates, and both are small. The expected gain is at the brief's 1.1×
threshold rather than clearly over it, so the stages are measured one by
one and C and D are done only if A and B land as predicted.
