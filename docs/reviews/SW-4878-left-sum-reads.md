**Verdict: SOUND WITH CHANGES.** Values and stuck forms are unchanged, so nothing new can be accepted by conversion. But the claim "same steps" is false in one case (a solved metavariable inside the number), where a native or number case can take up to 9 times the steps it took before. Change 1 below fixes it; the alternative is to correct the docs and accept a small work-budget narrowing, which is Matt's call (D3688).

Review of SW-4878 (`lane/SW-4878` at 35760b066, against `main`). Read only: nothing built or run.

## What holds

1. **Natives pass every error on and charge last** (Opus's point 1). In `native::run`, `run_partial`, `view_with`, `view_keeping` and `as_nat_with`, every call of the `force` parameter is followed by `?`; nothing matches on, maps or discards an error. The only charges (`number_words` in `run`, `Mul`, `DivFuel`) come after the last force on their path. So a run stopped by an ask has charged nothing.
2. **`ASKED` can't leak in normal running.** It is private to value.rs, set only in `force_or_ask` immediately before returning `Err`, and `force_or_ask` is handed only to `native::run` (in `run_native`) and `view_with` (in `branch_asked`); both callers take it before looking at the result, so the stand-in `Cancelled` never escapes, and a real cancellation (with `ASKED` empty) goes through `outcome?`. A nested machine started by `force` inside the native sets and takes its own `ASKED` before returning, so levels can't see each other's. The reference evaluator and the elaborator's own calls (`native::view`, `value::force`) never use `force_or_ask`. The one way to leave it set is a panic unwinding between the set and the take; optional hardening: `ASKED.set(None)` before each read.
3. **A forced call is found by the rerun** (point 2), for the same call: `Frame::Unfolded` keeps the unfolding under the current modes and epoch, so `get` returns it in the rerun and `force_now`'s shortcut takes no step. Everything the first run forced before asking was step-free (unforced values and kept unfoldings), with the exception in "The step claim" below.
4. **`Stack::pop` by position** (point 3) is right: segment positions are strictly increasing, a frame's position is the length after popping it, and only `push`, `push_segment`, `pop` and the literal in `unfold_folded_head` touch the two vectors. A refused push changes neither.
5. **`branch_asked`'s `NumCase` arm** (point 4): reads the saved forced scrutinee from the start with the same `view_with`; the frame keeps `tree`, `env`, `stuck`; the two `reread_sum` recursions restart at `asked = 0` with a new value, which is right.
6. **`AddNat` through `read_number(forced = false)`** (point 5) is `view_with` arm for arm: the first force included, and `finish` with `sum: None` gives `from_view(outer + k, base)`, the old result.
7. **Depth accounting:** each new waiting frame (`NativeAgain`, `NumberScrutinee`, `ReadNumber` from `AddNat`) stands where `force` started a nested machine, and the frames above it are counted from zero, as that machine counted them. The 200,000 cap now covers all segment kinds together; each was over a kilobyte of Rust stack before, and the largest configured stack guards 192 MiB, so no reachable run had 200,000 of them.
8. `resume_rare` handles the two new frames and its closing arm is still an explicit list, so the match is exhaustive.

## The step claim is false with a solved metavariable (change 1)

`force_or_ask` passes anything but an unkept call to `force`, which starts a nested machine for a solved metavariable, or for a call whose kept unfolding needs forcing again. That machine takes steps and builds **fresh** values, so a glued call in its result has a fresh, empty unfolding cell each time.

Case: during elaboration, a native's number argument (or a number case's scrutinee) is or contains `?m args`, with `?m` since solved to something that evaluates, glued, to `Succ (f y)` with `f` glued.

- Run 1: `force(?m args)` replays the solution (s₁ steps) and gives `Succ C₁`; `C₁` has no kept unfolding, so the native asks; the machine forces `C₁` (s₂ steps).
- Rerun: `force(?m args)` replays again (s₁ again) and gives `Succ C₂`, a different cell; ask again; the machine forces `C₂` (s₂ again).
- This repeats until the cap: 8 asks, then a ninth run with plain `force`. Total 9·(s₁ + s₂) against s₁ + s₂ before.

The value is the same (evaluation is deterministic and the cells only memoise), so this is not a soundness problem. It is a time cost, a work-budget narrowing (a declaration whose such forcing took over a ninth of its remaining steps is now refused), and it contradicts `ASKS`'s comment ("changes no value, step or limit"), `run_native`'s doc and docs/core.md ("takes the same steps").

**Change 1 (recommended fix):** stop asking once the read has forced anything through a machine. Add a thread-local flag beside `ASKED`; `run_native` and `branch_asked` clear it before the read; `force_or_ask` asks only if it is clear, and sets it after any `force` that was not step-free (set after `force` returns, so nested reads that clear it in between don't matter). Then every rerun repeats only step-free forcings, the step claim is exact, and `ASKS` remains purely the guard against quadratic rereading. Add a test with a solved metavariable inside a native's argument comparing step counts with `force`. If the fix is not wanted: correct the three texts to say steps can repeat up to eight times after a solved metavariable, and bring the narrowing to Matt.

## The refusal that doesn't mark the budget (change 2, not blocking)

`push_segment`'s cap returns `Depth` without `note_ran_out`, `exhausted` or `work_limit = 0` (as SW-4879's did on main; this lane widens it to natives and number cases). It is safe for soundness: no caller reads an error as success. But the elaborator takes an unmarked resource error to be an inner attempt's failure, not the operation's: `check.rs:7397` answers "not the same type" and carries on, and `equations.rs:2679` skips the equation. So the cap could surface as a type mismatch, or a silently different elaboration route, where the Rust-stack guard it replaces (which marks) gave `E-RESOURCE`; and the message loses "ran out in". Nothing is cached wrongly that I can see: the outcome is deterministic. **Change 2:** refuse through the budget, as the frame limit does (a small `Budget` method that notes, marks `Depth` and zeroes the work limit).

## Narrowing (D3688)

Only the work-budget case above, removed by change 1. The segment cap and frame counts refuse nothing reachable before.

## docs/core.md

Accurate except "finding the call's kept unfolding, so it forces the same parts in the same order and takes the same steps" and "which of the two forces a call changes only Rust stack and time": true once change 1 is in; false today for a solved metavariable inside the number.

## Not checked

Nothing was run. The new tests were read by name and doc only. Whether the metavariable case occurs in the repo's proofs I did not measure; it needs a number built before a metavariable was solved and read by a native or number case afterwards.

---

# Re-review of the delta 35760b066..107a988da (26 Nov, read only)

**Verdict: SOUND.** Both changes are made as asked and I found nothing further to change.

## `FORCED` and nested reads

- **An inner read can't clobber an outer read's `ASKED`.** `ASKED` is set only as the last act of `force_or_ask` before it returns the error, and the native passes that straight up to the taker; no evaluation, so no inner read, runs between the set and the take. When an inner read's `start_read` clears `ASKED`, the outer read's is already empty.
- **An inner read can't clobber an outer read's `FORCED` in a way that matters.** Inner reads run only inside a `force` that starts a machine, which is exactly the case `forces_free` reports as not free (a solved metavariable, or a call whose kept unfolding needs forcing; it mirrors `force` and `force_now`'s shortcut). `free` is computed before the `force`, and `FORCED` is set to true after it returns, whatever the inner reads left there. A free `force` starts no machine, so the outer flag is untouched. So after every `force_or_ask` the flag is the outer read's own.
- **A rerun after an ask starts clean** (`start_read` at the top of `run_native` and of `branch_asked`'s number arm), and the segment the machine forces in between starts its own reads the same way. `start_read` also covers the panic window I mentioned.
- **The step claim is now exact:** a read asks only while everything it forced so far was free, so a rerun repeats only step-free forcings, then finds the asked call's kept unfolding. Past the flag, or past eight asks, forcing is plain `force`, as before the lane.

## `Budget::too_much_pending` at the cap

- It is the frame limit's own code moved into a method (`note_ran_out`, keep the first error, mark, zero the work limit), and `frames` now calls it; no behaviour change there.
- At the cap, the refusal is now sticky like the frame limit's and like the Rust-stack guard it replaces. The only callers that behaved differently on main were those that took the unmarked `Depth` for an inner attempt's failure (`check.rs:7397`, `equations.rs:2679`); they now pass it on as the operation's, which is the intent. Inside a real attempt (`aside`, `start_attempt`) the mark is restored away when the attempt ends, exactly as for the frame limit, so attempts still fail locally.
- `note_deepest` is called only when the error is `Depth`, after the mark, the same order as `frames_for`.

## `set_never_ask`

Compiled under `test` or the `reference` feature; its only caller is the new test, which restores it. Its thread-local defaults to false, so a real check never takes that branch; and if it were set, natives and number cases would force with `force` alone, which is the behaviour before this lane: same values, same steps. It can't make a check accept anything.

## The new test (read, not run)

`?m x + 1` puts the solved metavariable where the native's read forces it (not free, so no ask for `slow x`), and compares result and step count with asking off. The `isTwo` half exercises a different path than its doc suggests: the machine forces the scrutinee before the read (`Frame::Scrutinee`), so the read does ask for `slow x`, and the rerun finds the same call's kept unfolding. Still a valid equal-steps check.

## docs/core.md

The added parenthesis is accurate, and with it "takes the same steps" and "changes only Rust stack and time" now hold.
