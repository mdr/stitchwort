**Verdict: SOUND.** No required changes. One acceptance difference for Matt to note (a contrived depth-limit case, below), and three optional edits.

Review of SW-4865 (stuck-sum read on the machine's own stack), commit 44b27902e on `lane/SW-4865`. Read only: nothing built or run; every claim below is from reading the code.

## Soundness: same values, same stuck forms

1. **`read_second` is `view_with` + `nat_add::stuck`, arm for arm.** The loop's five arms (`Nat`, `NatAdd`, `Zero`, `Succ` with one field, other) are `view_with`'s, with the same `nat` guard. Where `view_with` calls `force`, the loop does what `force`/`force_now` do: nothing if `!needs_forcing`; a call's kept unfolding if it has one that needs no forcing (the same two tests, no step); otherwise `Control::Force(next)`, which is exactly what `force_now` hands its nested `run`. The resumed value is matched without a second force (`forced = true`), as `view_with` matches `force`'s result directly. `read.k` lives in the frame, so the count survives each suspension.
2. **`finish` matches both old callers, case by case.** From `stuck_tree` (`outer = 0`): no base gives `from_view(k, m)` (old `Some((k, m))`); a base with `k = 0` gives `Neutral(Def(id), spine)` with the original spine (old `None` branch); a base with `k > 0` gives `from_view(k, call(id, m, base))`. From `run_native` (`outer = k`): `from_view(k + k2, m)`, `from_view(k, call(id, m, n))` with the unforced `n`, and `from_view(k + k2, call(id, m, base))`, which are the three results of the old `run_partial` arm. Rule not bound to `id`: `stuck_tree` tests `nat_add_rule == Some(id)` before reading (as `stuck` did first), and `run_native` returns `from_view(k, call(id, m, n))` without reading `n` (old: `stuck` returned `None` before `view_with`). So no forcing happens for an unbound `add` in either version.
3. **The shared stack is opaque to the forcing.** A machine's frames are only ever pushed (`push`) and popped (`Control::Return`); nothing peeks, truncates or unwinds. The one reader of lower frames is `note_deepest`, which only builds the "recursing too deeply" message. So the steps taken from `Control::Force(part)` to the matching `Return` are those of the old nested machine started with an empty stack. No mode (`glue`, erasure) was scoped around the old `force` call, so there is nothing a nested run restored that the frame version misses.
4. **No caller post-processes the returned `Control`.** I checked all 20 call sites of `unfold`, `unfold_now`, `from_native`, `run_native`, `branch`, `stuck_tree` and `read_second`: each returns the control straight to the run loop, and every frame that must sit below a possible `ReadSecond` (`Unfolded` in `force_call`, `AddNat` for `UnfoldAfterSuccs`) is pushed before the call. `unfold_once` builds its stack first and passes it to `run_on`.
5. **Errors mid-chain** (budget, depth, cancel) return `Err` through the loop and drop the stack; before, they propagated through the nested Rust frames and dropped the same pending work. No `Unfolded` frame sets its cell on the error path in either version, and the budget's `exhausted` is sticky in both.
6. **Re-entrancy / a part that is itself a chain:** the forced part's own stuck sum pushes its own `ReadSecond` above this one; each frame owns its `m`, `stuck`, `outer`, `k`, with no shared state. Solved metavariables go through `Frame::Replay` as before.
7. **`resume` / `resume_rare` split:** all 33 `Frame` variants are handled exactly once; no variant is split across the two functions; the guarded arms of each variant keep their order (`ProjOf`, `ProjForced`, `Scrutinee`, `LiftForced` in `resume`; `JForced`, `CallField` in `resume_rare`).
8. **Reference evaluator:** `native::add_stuck` is the old `run_partial` code moved; its stuck-tree site (reference.rs:582) still calls `nat_add::stuck`. Behaviour unchanged, still recursive. Kernel and reference normal forms agree as before.
9. **Step counts** are unchanged, as argued: the nested run took one step per loop iteration, from `Force` to the final `Return` (popping nothing); the frame version takes the same iterations, the last popping `ReadSecond`. The kept-unfolding shortcut takes no step in either. (Test-only `RUNS` falls; `peak_frames` rises, since one stack now holds what several did.)

## Acceptance

- **Pure chains: more is accepted.** Before, each link cost a nested machine on the Rust stack (3 KiB in wasm), ended by the stack guard: at most about 16,000 links on the CLI's 64 MiB thread and 64,000 on the web's 256 MiB (estimates: guarded stack ÷ 3 KiB; native frames are larger). Now a link is two or three heap frames, so the 2,000,000-frame limit is reached near 700,000 links. No configured stack reached that before.
- **One case newly refused** (for Matt; contrived, I recommend accepting it): the frame limit counts one stack, where each nested machine had its own 2,000,000. A run that has `F` frames pending when a stuck `m + n` needs `n` forced, where that forcing peaks at `f` frames, was accepted when `F ≤ 2,000,000` and `f ≤ 2,000,000`, and is now refused (`E-RESOURCE`, depth) when `F + 1 + f > 2,000,000`. Example shape: a non-tail recursion about 1,000,000 frames deep whose innermost call computes `x + g k x`, with `g` another non-tail recursion about 1,000,000 frames deep. It needs millions of pending frames on both sides of one sum. Forcing a scrutinee or a native's number argument already shares the stack this way; the separate allowance was a side effect of the nested call.
- Step and work budgets: no change (point 9).

## docs/core.md

The new sentence is accurate. Optional addition: say that these frames count towards the run's depth limit.

## Optional edits (none blocks the merge)

1. `resume_rare` ends in `_ => unreachable!(...)`, so a future `Frame` variant missing from both functions compiles and panics at run time. Replace `_` with an or-pattern naming the frames `resume` takes, to keep the compiler's exhaustiveness check.
2. Test gap: no test makes `ReadSecond` suspend with `outer > 0` (in `succChain` the second argument is already forced by `NativeArg`, so the kept-unfolding shortcut applies), nor with `k > 0` carried across a suspension. A pair such as `g (Succ k) x = Succ (h k x)`, `h k x = (x + 1) + g k x` does both (`h`'s sum reads `Succ (h …)` with the inner call unforced); compare the machine's normal form with the reference's.
3. `read_second`'s doc says the frames below "are never looked at until it returns": add "except to count them for the depth limit and its message".

## Not checked

Nothing was run: the new test, the wasm stack figures and the step-count claim are unmeasured here. The first argument's side (`view(m)` in `run_partial`, `Frame::AddNat`'s `view_with`) still forces through nested machines; out of this change's scope.

---

# Re-review of the delta, commit 0ef63eae8 (26 Nov, read only)

**Verdict: SOUND.** No required changes. One doc wording fix and one robustness note, both optional.

## `Stack::push` / `pop` / `counted`

- **The positions can't desync.** `frames` and `reads` are touched in exactly four places: `push` (records `frames.len()` just before pushing a `ReadSecond`), `Stack::pop` (drops the last position when the popped frame is a `ReadSecond`), `counted` (read only), and the literal in `unfold_folded_head` (one `Replay`, no reads: consistent). There is no direct `stack.frames.push/pop`, no truncate, clear, drain or bulk pop anywhere in value.rs; the run loop's only removal is `stack.pop()` at `Control::Return`. Frames are strictly LIFO, so the last entry of `reads` is always the topmost `ReadSecond`'s index.
- **A refused push changes nothing:** the budget check comes before both `reads.push` and `frames.push`.
- **Errors** drop the whole `Stack`; there is no partial unwinding to leave it inconsistent.
- The frame nested in `Frame::Unfolding` is pushed later through `push` like any other.
- `resume_rare`'s final arm now names the 21 frames `resume` takes (I checked the list against `resume`'s arms: complete), so the match is exhaustive again.

## Is anything accepted before 44b27902e now refused?

No, with the one theoretical exception below.

- **Ordinary frames:** a push is checked against `counted().len() + 1`, the frames above the topmost `ReadSecond`. Those are exactly the frames the old nested machine (started empty by `force`) held, and when the read is popped the count is the outer segment's again, as when the nested machine returned. This holds at every nesting level, so each depth check compares the same number with the same limit as before 44b27902e. `note_deepest` gets the same slice the nested machine would have given it.
- **Pending reads:** refused past 2,000,000 nested reads. Before, that needed 2,000,000 nested machines on the Rust stack, over 2 GiB at more than 1 KiB each; the largest configured stack is 256 MiB (web), 64 MiB on the CLI, and I found no user setting for it. So nothing reachable is refused.
- Step counts are as in 44b27902e: this commit adds no steps.

## The endless-chain bound

It stops: reads are capped at 2,000,000 and each segment at 2,000,000 frames, and every push is a counted step, so the work budget (10 billion) is the final backstop, as it was before 44b27902e.

Robustness note (not soundness, optional): the cap on total heap is looser than under 44b27902e alone. A thin chain (two or three frames a link) can now hold about 6,000,000 frames (`Frame` is at most 64 bytes) plus 2,000,000 boxed `ReadSecond`s before it is refused: several hundred MB, perhaps near 1 GB with the vector's growth (estimated, not measured), where the single shared count stopped at 2,000,000 frames (128 MB). Before both commits the stack guard ended such a chain at about 16,000 links (CLI) or 64,000 (web). In the browser a 2,000,000-link chain may therefore run out of wasm memory instead of reporting `E-RESOURCE`. Worth a small ticket to measure, not a reason to hold the merge; if it matters, cap pending reads lower (anything above about 200,000 still refuses nothing a configured stack reached).

## docs/core.md

"so what's accepted doesn't change" is not quite right: long chains that ran out of Rust stack are now accepted. Suggested: "so nothing accepted before is refused".

## Tests (read, not run)

- `a_read_keeps_its_count_across_a_forced_call`: `g`'s `Succ (wrap …)` with `wrap` glued does make the read suspend with `outer = 1` and `k = 1`, and it compares against the reference evaluator, glued and not. Covers the gap I named.
- `a_read_counts_its_forcing_against_the_depth_limit_on_its_own`: with a 3,000-frame limit, 1,000 + 1,000 passes and 2,000 + 0 is refused. This relies on a level costing more than 1.5 and at most 3 frames; I count two (`NativeArg`, `Unfolded`), which fits, but I did not run it.
