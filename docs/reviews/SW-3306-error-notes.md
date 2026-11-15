# SW-3306 + SW-3299 review: partial unification before a call's searches

Reviewer: Opus, 15 Nov 2026. Branch `lane/SW-3306` (acdeffbef), against `main`
at b1e5025c8. Probes: `sw3306-review/p1.sw` … `p7.sw` in the scratch folder,
each checked with both release binaries (`run.sh`).

## Findings

### F1 (medium; fix before merge): ill-typed solutions on rejected programs

`unify_what_agrees` keeps solving after a rigid clash, including a clash in a
*type* that a metavariable's type depends on. The unifier doesn't check a
solution's type, so the metavariable gets a value of the wrong type. The
call's searches then run against goals that make no sense, and their error
replaces the real type mismatch (only one error per declaration).

```
type P (a: Type) (x: a): Prop = { holds: x = x }
theorem lem ∀ [x: Nat] (h: x + 1 = 3): P Nat x := { holds = rfl }
theorem use: P Bool True := lem rfl
```

- main: `expected P Bool True, but this has type P Nat 2` (the real error)
- branch: `` `Succ True` and `3` aren't equal `` (`?x: Nat := True`)
- with `omega`: main says the goal has unknowns; branch says
  `` omega can't prove `True + 1 = 3` `` (atoms: `True`).
- More of the same (p6, p7): `True.second`, `pick [3]` (a List matched as an
  Option), `rest (Some 3)`, `Std.List.length 5`. In those cases main was poor
  too (it showed `?0`), but the branch's text describes terms that can't
  exist. The evaluator got stuck rather than panicking in every probe, so I
  found no crash.

Only programs that are already wrong are affected (see F2), so this is about
message quality, not soundness. But SW-3299 exists to make these messages
better, and this makes a class of them worse.

**Fix (proposed):** keep the partial solutions only when no rigid clash is
between *types*. While `unify_what_agrees` runs, note whether a clashing pair
is a type (a sort, a Pi, or an applied type former / data type head). If one
is, restore to a mark taken before the call and fall back to main's
behaviour. The SW-3299 case clashes on values (`(second, first)` against
`(first, second)`), so it keeps its improvement; p5–p7 clash on `Nat`/`Bool`,
`R`/`Bool` and `List`/`Option`, so they go back to main's messages. Index-only
mismatches (`Fin 3` against `Fin 4`) would still leave a solution whose type
is off only in an index. That is harmless to evaluate, and acceptable. The
more thorough alternative is to check each new solution's type against its
metavariable's (`meta_type`). Elab has no ready inference for a core term,
though, so that is more work. Add p5's `use` as a reject example with the
fix.

The orchestrator's suggestion, "only on the error-reporting path", doesn't
fit as it stands. The searches run before the final comparison, so by the
time that comparison fails, the search error has already been produced. The
type-clash guard gets the same effect without moving anything.

### F2 (none found): can a correct program now fail?

I tried to construct one and couldn't. Here is why I think the change is safe
for programs `main` accepts:

- On a correct program the final comparison succeeds. So any failing pair at
  this point is *flexible*: blocked or stale on an unknown that the searches
  or instances will fix. A rigid clash can't occur.
- The pairs `unify_what_agrees` solves come from the same decomposition the
  final comparison makes: rigid constructors, Pi, and record fields. Two
  calls of one definition are compared by their arguments with nothing
  solved (`same_arguments_solving_nothing`), then unfolded, as before. So
  every solution it commits is one the final comparison would also require.
  Committing it earlier only gives the searches more information.
- The one decomposition that isn't forced is the lossy spine comparison of
  two calls of one definition stuck on an unknown (`same_heads`, blocked
  branch). It runs nested and is **not undone when it fails**, so
  `unify_what_agrees` keeps part of a failed spine. Example: `f ?b ?k 1`
  against `f c 5 2` keeps `?b := c, ?k := 5`. For main to accept such a
  program, the final comparison would have to make `f e k' 1` equal to
  `f c 5 2` with different arguments. I tried this (p1–p4, a `match` that
  ignores `k` and `n`). Main rejects it too: solved unknowns still count as
  "may mention an unknown", so the final comparison compares spines in
  shortcut mode rather than case trees. So there's no counterexample today.
  It does depend on that shortcut behaviour, though. If the final comparison
  ever compares such calls by unfolding (or by case trees once the unknowns
  are solved), this becomes a real way for the branch to reject a correct
  program. Worth a sentence in the doc comment, or simply undoing a failed
  nested spine run inside `unify_what_agrees`.
- Implicit arguments next: guarded by `implicit_next`, as before. Under
  binders: solutions go through pattern unification, the same as the final
  comparison. Instances: `solve_ready_instances_keeping` runs after, with
  more solved, and finds the same instances.

Minor side effects on correct programs:

- `note_rigid_divergence` (`unify.rs:813`) is sticky and isn't restored by a
  mark. Going past the first failure can now set it where main's
  stop-at-first-failure comparison wouldn't. It only matters when a body then
  fails.
- `unify_what_agrees` can return `Err` when the budget runs out. That error
  propagates (`?`) on a path whose failure was ignored before. The cost is
  bounded by the size of the values, so it's unlikely, but it is a new way to
  fail.

The path runs on correct code often. One check of `Aoc.Year2020.Day02.Proofs`
hit it 9 times (instrumented, since reverted). Each time it was either
filling a spec `_` from the expected type (`readsLine`'s `readsDone`) or
unifying one unknown with another (`?28 := ?13`).

### F3 (ok): `differ_beyond_unknowns` and mark/restore

`Attempt::restore` takes back the metavariable trail and new metavariables,
`lossy`, the keyed tables, obligations, row metas and constraints, and the
queue (including taken-back fills of `lifted_calls`). `call_memo` is a fresh
scoped guard inside `unify_what_agrees`. `waiting` is `None` under
`nested`, so nothing is put aside. Two things are not restored:

- `rigid_divergence` and `instance_steps`, by design. `undo::unify` doesn't
  restore them either.
- the presentation counters that `undo::Snapshot` adds (`pending_local_types`
  / goals / steps). The unifier doesn't touch them.

An `Err` there restores the mark and reads as "no clash", which is right for a
note.

### F4 (ok): the `readsLine` term change

The statement is written out in full (`Parse.Reads line Written`, no holes),
so its elaborated type can't change. Only the proof term differs. The cause
is the probe above: `readsDone`'s spec `_` (`?57`) is now solved from the
expected type before its `rewrite … in Witness …` search runs. Before, it was
solved from the call's last comparison afterwards. That is migration cost
only.

### F5 (messages; nothing misleading)

- `match-equation-leaves-solution`: dropping "give it with `[n := …]`" is
  right. The sides also clash at `None`/`slot.field` and `4`/`5`, which giving
  `n` wouldn't fix. One caveat: the advice is dropped whenever there's *any*
  rigid clash, even where giving `n` would fix part of the mismatch. Fine.
- `reads-chain-swapped-pair`: the new error (`` `[first, second]` and
  `[second, first]` aren't equal ``) names the actual problem. Good.
- `reads-weaken-over-map-implicits`, `settle-from-expected-wrong-row`:
  dropping "`t` was taken as `Char`" is right. The mismatch is elsewhere (the
  `St` row, the spec). `is_about` matches by printed text, so a `given` whose
  printed form happens to appear in an unrelated place keeps the note. That's
  harmless, since the note is still true.
- The snapshots' `source:` header changed to `crates/cli/tests/examples.rs`,
  a file that no longer exists. That's churn, not a problem: 970 of the
  snapshots in that folder already have that header and 228 have the
  `running/` one. Insta ignores the header when comparing.

## Verdict

**Merge after fix.** I couldn't make a correct program fail. The solutions
committed early are ones the final comparison forces anyway, and the one
unforced case (a failed spine of stuck calls) is rejected by `main` too
today. The message changes are accurate, and SW-3299's target message is much
better. But continuing past a rigid clash in a *type* commits ill-typed
solutions, so for a family of wrong programs the clear "expected `P Bool
True`, but this has type `P Nat 2`" turns into errors about `Succ True`,
`True.second` or `pick [3]`. That runs against the point of the ticket.
Guard it: restore when any clash pair is a type (F1). Add p5's `use` as a
reject example. Optionally undo a failed nested spine run inside
`unify_what_agrees`, so F2's argument doesn't rest on the shortcut-mode
detail.
