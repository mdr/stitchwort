**Verdict: SOUND.** No required changes. The 2 GB fuzz finding is not caused by per-segment frame counting, as far as the code shows; see the last section.

Review of SW-4881 (`lane/SW-4881`, commit 40d58c113, against `main`). Read only: nothing built or run.

## Opus's five points

1. **`Folded::go` is the old `unfold_folded`, state for state.**
   - `Idle`: not folded gives `current` (old `return Ok(current)`); otherwise the same `folded_parts`, tree and `Some((id, call, false))`, as `FoldNeed::Run`.
   - `Ran`: the same stuck test (`id2 == id` and `ptr_eq`) gives `current`; no fields and `needs_forcing` asks for the force and then keeps `forced` only if `folded_call(forced)`, else `next`; no fields otherwise sets `current = next`; with fields, forces `next` for field 0.
   - `FieldBase` → new level (the old recursive `unfold_folded(&base)`), with the forced base kept in `FieldInner`. When that level finishes: `Some(unfolded)` is forced (`FieldUnfolded`) and the field taken of the result; `None` takes the field of the saved base. That is the old `match unfold_folded(g, &base)? { Some(u) => force(u)?, None => base }`.
   - `field`: `project`, then either `current = next` (last field) or a force of `next` for field `i + 1`, the old `for` loop's next turn.
   - `unfold_folded` itself now drives the same code with `run` and `force`, so conversion and the other callers are unchanged.
2. **`Walk` is the old `reread` loop.** `viewed` (not reading) has the old three arms: no base and a folded `k * x` read the sum; any other base asks for the unfold. `unfolded` has the old two: something unfolded rewrites `sum.n` and views again; nothing unfolded goes down into a sum not in `unread` (the step charged at the same point) or reads the sum. `read_sum` plus the `reading` branch of `viewed` are `Sum::read` and `stuck_value`: nothing if the sum has nothing unfolded, else `k + m`, nothing for `k = 0` over a base, or `k + add m base`. `climb` matches the old inner loop: a read handed up rewrites the parent's `n` and goes on walking it; no read reads the parent if it has something unfolded, else pops on. Setting `sum = parent` first is needed (the `reading` view reads `self.sum`) and harmless where the parent is passed over. `unread` is extended only at `Done`, as before; on an error `reread` puts the taken `Unread` back unchanged.
3. **`reread_go`'s three `push_segment` sites are exactly where a machine started:** a number part that isn't free (old `view_with`'s `force`), a case tree run (old `run`), and a force inside the unfolding that isn't free (old `force`). `forced_free` mirrors `force` and `force_now`'s no-machine paths; `read_on` is `read_number`'s loop unchanged, now shared. Each resumed frame adds no step of its own, so step counts match the nested runs.
4. **`AfterReread::finish` matches both old sites.** Number case: `from_view(k, read)` then `branch_asked(…, 0)`, or `stuck_tree`, with no count, as before. Constructor case: `branch_asked` on the read, or `count_stuck_one_shape` (only reached with a `Term::Case`, so `d` is the old `*d`) then `stuck_tree`. A value that isn't a sum finishes at once with nothing, taking no step, as `reread_sum` returned `None`.
5. **`run_float` / `unfold_unless_float`:** the order in `unfold_now` is unchanged (hidden or frozen, erased, float, native, case tree). `float::run` and its helpers (`known_bits`, `known_int`, `as_nat_with`) force only through the parameter, pass every error on with `?`, and charge nothing, so the SW-4878 argument applies: a rerun repeats only step-free forcings. A `FloatAgain` rerun skips the three earlier checks, which can't have changed.

## Other checks

- `set_nested_reread` is compiled only under `test` or `reference`; its one caller is the new test, which restores it; default false. If set it takes the old `reread_sum` path: same values and steps. It can't affect a real check.
- `resume_rare` handles `FloatAgain` and `Reread`; its closing list is explicit, so the compiler checks coverage.
- `ASKED` / `FORCED`: the walk never uses `force_or_ask`; `run_float` starts its read with `start_read` like the others.
- **Narrowing:** none found. The new segments count against the 200,000 cap; each was a nested Rust machine before, so no configured stack reached it.
- **docs/core.md:** both additions are accurate.

## Not checked

Nothing was run; the step-count test was read, not executed. I did not re-read `to_int_value` for a charge (it runs after every force, so it could not be repeated by a rerun anyway).

## The 2 GB fuzz finding (`count 6000000`)

From the code, this one is not pending frames, so no frame cap would refuse it.

- `count (Succ n) = Succ (count n)` evaluated glued gives `Succ (glued call)`. The comparison reads it with `view_with(force)`: each link's forcing runs to `Succ (next call)` and returns before the next starts. Pending frames stay constant, and the steps (a few per link, tens of millions) are far under the 10 billion budget.
- The heap is the value: every forced call keeps its unfolding, the unfolding holds the next call, and the root call keeps the whole chain alive. That is a call, a spine, an `Unfolding` cell with its modes and a constructor per link; at an estimated 300 to 350 bytes a link (not measured), 6,000,000 links is about 2 GB. Nothing counts it: the frame limit sees no depth and the size limit applies to read-back only.
- This path (conversion's own `view_with` with `force`) is untouched by SW-4865, SW-4879, SW-4878 and this lane, so I expect the commit before SW-4865 holds the same memory; Overmind can confirm by running it there.
- A bound that fits: charge kept unfoldings (or values allocated) to the operation and refuse past a cap. That is a new resource limit with a user-visible refusal, so it is a design for Matt, not a fix to fold into this lane.

On total frames across segments: per-segment counting does allow a total over 2,000,000 (up to 200,000 segments of up to 2,000,000 frames each), but so did nested machines before (each had its own 2,000,000), so no total cap "refuses nothing reachable before" in the strict sense. A practical cap of 8,000,000 frames in all (about 512 MB at 64 bytes a frame, refused through `Budget::too_much_pending`) would refuse only runs with at least four forcings nested in one another, each over a million frames deep. That is a narrowing in principle, so Matt's call; I'd recommend it as cheap protection for the browser, filed separately.
