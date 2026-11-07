# Review of SW-1998, SW-1995 and SW-2086 (SW-2094)

*7 November 2026. A fresh-eyes review by reading only: nothing was built,
tested or run. Line numbers are at `429039bd2` (`main`). The merges:*

- `8482b8cf0`, **SW-1998** (unifier, Opus): a field of an unsolved unknown
  counts as blocked (`blocked_within`). A stuck field of a kept call is
  compared by the call (`same_field_records`). The SW-1913 workarounds come
  out of 2020 day 20 and 2021 day 11.
- `caf327238`, **SW-1995** (Sonnet): `rewind_globals` calls
  `Kernel::forget_since`, not `rewind`.
- `45169c4e4`, **SW-2086** (lsp, Sonnet): reopening runs under the catch,
  each edit costs one restart, diagnostics are recorded only after they
  are sent, and `workspace_of`/`home_of` give one workspace rule. This
  follows SW-1948 and its review,
  `docs/reviews/SW-2087-checker-recovery-and-forget-since.md`.

*Read as well: `docs/proposals/record-eta.md` §8,
`docs/proposals/record-eta-remaining.md`,
`docs/reviews/record-eta-as-merged.md`, `docs/repros/sw-1913/` (including
the reverted `unify-fixes.patch`), `docs/research/rust-codebase-review.md`,
and the tickets SW-1914, SW-2078, SW-2088 to SW-2093.*

## Summary

**All three merges are sound, and none needs reverting.** SW-1998 can't make
Stitchwort accept something false. Every declaration still goes through
the kernel, and both new rules only build values that are equal by
definition. `Value::Call(f, args)` means `f args`, and a field of an unknown
stays one. Nor can it loop. A pair it postpones is tried again only if
something was solved since it was put aside, and each pass is charged to
the budget. The one weak spot is its tests: the
boundary the new comment states ("counts as that call did, and no
further") has no test that pins it, and the reject example would be
rejected with or without the change. SW-1995 is right. All four callers
run after `attempt` has restored the operation's budget, and the test
fails on the old code, though it checks only the size limit. SW-2086
fixes C1's main path, C4 and C5, and C2's retry rule, and its new tests
for C1 and C2 can fail. It opens one new gap. When it blames a panic on a
workspace, it reads and parses the project *outside* the catch. So a
panic in reading a project now happens twice, and the second one stops
checking everywhere. The C5 test passes on the old code too.

**Top five recommendations**

1. **Blame a panic without risking a second one** (L1, medium). In
   `Checker::caught`, compute the workspace under its own catch, falling
   back to `find_project` or the path. Or compute the key before running
   `f`. Then a panic in reading `stitchwort.yaml` or the source folders
   quarantines that project instead of stopping checking. S.
2. **Pin SW-1998's boundary with tests** (U2, medium). Three cases: a
   frozen unknown's field isn't blocked, an unknown applied to arguments
   alone (`?m x`) isn't blocked, and `(?m x).f` is. Add one more
   `same_field_records` case with gluing off (it stays the neutral). S to M.
3. **Stop `home_of` reading every source file** (L2, low). Today it reads
   every `.sw` file in the project to decide whether one path is a source.
   It runs on every new workspace (and `load_project` then reads them all
   again), and on every quarantine lookup. Ask the source only for the
   config's `sources`. S.
4. **Make the C5 test able to fail** (L4, low). Close the quarantined loose
   file and expect empty diagnostics, or keep the fault armed and expect
   it to be quarantined again after one restart. Both differ on the old
   code. S.
5. **Correct the misleading comment, and say what SW-1998 changed in
   `record-eta.md` §8** (U1, U6, low). The narrowing to `is_folded` doesn't
   leave out a stuck call that was then projected: that has the same shape,
   and is compared as the call. The design note doesn't yet say that a
   field of an unknown waits, or that a call's field is compared by the
   call. S.

**Counts:** 0 high, 2 medium, 12 low.

## Findings

| # | Where | Finding | Sev | Conf | Size |
|---|---|---|---|---|---|
| L1 | `lsp/src/lib.rs:2676-2687`, `:2615-2625` | `caught` works out whom to blame (`workspace_of` → `home_of` → `Source::project`, which reads and parses the project) in `map_err`, outside the catch. A panic in reading a project happens again there, escapes the thread and stops checking for every project. Before SW-2086, `workspace_of` only called `find_project` | medium | high (path), low (how likely such a panic is) | S |
| U2 | `elab/src/unify.rs:1225-1240` | No test of the new `blocked_within` arm's limits: frozen unknown, `?m x` without a projection, `(?m x).f`. Only the examples and AoC cover it, and they don't check the "no further" side | medium | high | S-M |
| L2 | `lsp/src/lib.rs:2615`, `:3175`, `source.rs:65-91` | `home_of` calls `Source::project`, which reads every `.sw` file under the source folders. That happens for each new workspace (then `load_project` reads them all again), each `quarantine_key` lookup while anything is quarantined, and each other open file in `edited`. A broken `stitchwort.yaml` is also logged on every call | low | high | S |
| L4 | `lsp/tests/it/faults.rs` (`a_file_on_its_own_in_a_project_folder_is_quarantined_by_its_own_key`) | Passes on the old code: the fault is cleared before the edit, and the old `apply` checked the file anyway (SW-2087 C5's first bullet). It doesn't show that the keys agree | low | medium-high | S |
| L5 | `lsp/src/lib.rs:2706-2711`, `:2654` | C1's third bullet isn't done. `into_keeper` drops the sessions inside the thread before the `Keeper` is returned, so a panic in a session's `Drop` there loses the `Keeper` (a full stop, with stale diagnostics on screen) | low | medium | S |
| L3 | `lsp/src/lib.rs:3474-3485` | `relative`'s doc line was left above `sources_hold`'s doc: rustdoc shows `sources_hold` starting with "`path` within the folder `dir`…", and `relative` has no doc | low | high | S |
| L6 | `lsp/src/source.rs:194-201` | A third copy of "is this a source file": `MemorySource::project`'s `within` doesn't trim a trailing `/` as `sources_hold` does. So the in-memory source the tests use can disagree with the rule it stands in for (`src/` lists nothing) | low | medium | S |
| L7 | `lsp/src/lib.rs:3040`, `:3000-3024` | An `Open` counts as an edit: opening any file of a quarantined project (a peek or go-to-definition opens one) lifts the quarantine and costs a restart. That is policy (D2741 says "edit"); see D3000 | low | high | S |
| U1 | `elab/src/unify.rs:1712-1718` | The comment says any other `Def` head "is a definition that is stuck, and stays one". But `is_folded`'s shape test (arity `App`s, then only `Proj`s, body seen) also matches a transparent call that got stuck and was then projected, so that is compared as the call too. That's harmless, because `Value::Call` means the call. It costs a re-run of `f x` (fresh `Unfolding`, the SW-1914 shape) | low | medium | S |
| U3 | `examples/reject/implicit-record-from-field-of-unknown-differs.sw` | The reject example would fail with or without SW-1998: `image.flip`'s rows and `image.rotate`'s differ whatever solves `?b`. It's a sanity check, not a pin. Nothing tests the lossy edge: a two-field record whose guess from one field (`?b := x` from `?b.f ≡ x.f`) a later field contradicts | low | high | S |
| U5 | `crates/cli/tests/running/snapshots/…differs.snap` | The new error prints the expected type as `Within`'s unfolding (`x ∈ image.flip.rotate.rows → x ∈ image.rotate.rows`), next to an actual type that stays folded (`Within image.flip image.flip.rotate`). `Within image.rotate image.flip.rotate` would read better. I haven't found the cause: look first | low | low | S-M |
| U6 | `docs/proposals/record-eta.md` §8, `record-eta-remaining.md:44-50` | Neither describes SW-1998's two rules (a field of an unknown waits like the accessor call did, and a call's field is compared by the call) | low | high | S |
| U4 | `elab/src/unify.rs:283-285`, `:1231` | SW-2078 interplay. SW-1998's note says it adds a route to `project`'s panic. It adds less than that suggests: `blocked_within` already forced `v` at its top before SW-1998, and so did `note_unfilled`. The only new step is the `Later` retry's `afresh`, which reaches the same `project`. No new ticket; a correction for SW-2078's brief | low | medium | - |
| S1 | `elab/src/kernel.rs:224-258` | SW-1995's test checks only `size_limit`. Nothing checks that the stack floor or a noted cancellation survive, or the path through `one_equation`/`function_induct` (a skipped equation followed by a declaration that runs out) | low | high | S |

## Details: SW-1998

### What changed, and why it's sound

**`blocked_within` (`unify.rs:1222-1258`).** A value that forces to
`Neutral(Meta m, spine)` with a projection anywhere in its spine counts as
blocked unless `m` is frozen. It doesn't recurse further. That changes
behaviour in two places only:

- **`run`'s put-aside (`:283-285`).** A failing pair with such a side goes
  to `Task::Later` instead of failing at once. `Later` is retried only if
  the meta trail has grown since it was put aside (`:294`). Otherwise it
  goes to `sets_aside`, as before. Every pass calls `budget.step()`. So
  retries are bounded by the number of solutions made, and there's no
  loop. The cost is one `afresh` (quote, then eval) per retry, which is the
  existing shape for definitions stuck on an unknown.
- **The all-unknown-arguments rule (`:1286-1295`).** `Call(R.f, [?b])`
  against `Call(R.f, [x])` used not to count as blocked, because forcing
  the first gave `?b.f`. Now it does, so `?b := x` is solved from the
  arguments and noted as lossy. This is the route that makes
  `examples/accept/implicit-record-from-field-of-unknown.sw` work, and it
  is exactly what the unifier did before record eta. The example's comment
  ("a call stuck on `?b`") describes it correctly.

Rule 1's guard (`:1655`, `!blocked(g, n)`) can't see the new case: a
neutral with an unknown at its head is taken by the arms above (frozen,
`same_field_records`, `solve`/`first_order`), so rule 1 never meets one.
The argument loop's `Neutral(Head::Meta(m), _)` arm already counted
an argument like `?r.f` as blocked before SW-1998. So the change is
confined to the value itself.

**`same_field_records` (`:1696-1735`).** Suppose the non-unknown side is
`Neutral(Def f, [args…, Proj…])`, gluing is on and `is_folded` holds. Then
its record is `Value::Call(f, spine without the last Proj,
Rc::default())`. That is well formed. If more projections remain, it's a
field call, which `force_call` handles through `unfolding.base` (`None`, so
the base call is computed afresh) and `Frame::CallField`. The read-back at
`core/src/value.rs:2608-2614` builds the same shape. The meaning is `f
args`, or its field, which is the value the stuck neutral stood for, so no
solution can be wrong. A wrong guess is undone (`undo_since`) or noted as
lossy, as before. Each nested `run` works on records with one projection
fewer on the unknown's side, so the recursion is bounded by how deep the
projections go.

**Soundness backstop.** `elab/src/kernel.rs` passes every declaration and
definition through the kernel in its own modes (D2294). If the unifier
says "equal" wrongly, the kernel refuses the term: no false theorem gets
in.

### U1. The comment overstates the narrowing (low)

The reverted patch turned every `Def` head into a `Call`. The merge adds
`is_folded`, and its comment says any other `Def` head "is a definition
that is stuck, and stays one". But a transparent `g` whose call `g x` got
stuck, and was then projected (`project` appends `Proj` to the neutral),
gives `Neutral(Def g, [x, Proj i])`. That's the same shape as a stuck field
call, and `is_folded` (`core/src/value.rs:2152-2161`) accepts it. It is
then compared as `Call(g, [x])`, which forces by running `g x` again. That
is correct and costs one re-run, the SW-1914 shape. **Change:** say in the
comment that the shapes can't be told apart and both are compared as the
call; what stays neutral is an opaque or sealed definition (no body seen),
gluing off, or an over-applied call. S.

### U2. The boundary has no unit test (medium)

The examples check that the two AoC shapes are accepted. Nothing checks
what the new arm leaves out, though the comment calls that the design ("no
further"):

- a frozen unknown's field (`?p.f` with `?p` an unfilled placeholder) is
  not blocked (it fails or waits through `sets_aside`, as before);
- `?m x` is solved, not put aside;
- `(?m x).f` and `?r.f x` are put aside, the latter being the widening from
  the patch's "last is a projection" to "any is";
- with gluing off, `same_field_records` keeps the neutral record.

If someone dropped the `frozen` check, or turned `any` into `last`, only an
AoC proof might notice, and possibly none would. **Change:** `unify.rs` has no test module, and the unifier is tested
almost entirely through `examples/`. So add small accept and reject
examples for the first three cases (a frozen placeholder through a
literal waiting for its type, an applied unknown, `(?m x).f`). Then, if
the lane can build the values cheaply, add a `#[cfg(test)]` module for
`blocked_within` and the gluing-off case. M.

### U3. The reject example doesn't pin the boundary (low)

`withinApart` fails because `image.flip.rows` and `image.rotate.rows`
differ, and it would have failed before SW-1998 too, with the old explicit
arguments. It shows that a solution guessed from a field is still checked,
which the kernel guarantees anyway. Here is what would pin something new:

- **The lossy edge, as a known limitation.** In `type P = { a: Nat, b: Nat
  }`, `?p.a ≡ x.a` guesses `?p := x`. A later `?p.b ≡ y.b` then fails,
  though `{ a = x.a, b = y.b }` would satisfy both. That's not a
  regression, since accessor calls behaved this way before eta (D2511),
  but a test would record it.
- **A `(f x).i` reject**, where `?c.grid.rows` is compared with a call's
  field whose grid differs from what a later link says.

S. As with any new example, the brief needs `snap:hashes` and the
`hash_stability` test.

### U4. SW-2078 (low, no new ticket)

SW-1998's ticket note says the change "adds one narrow route" to the
`project` panic: `?r` solved by `first_order` with a value of another type,
then its field re-evaluated. `blocked_within` and `note_unfilled` forced
`?r.f` before SW-1998 too, and forcing a solved unknown's field goes
through `ReplayElim` and then `project`. The only new step is the `Later`
retry's `afresh`. SW-2078 should start its search for a repro from
`first_order` solving an unknown whose field already exists, whichever
path then forces it.

### U5. The reject message prints one side unfolded (low, low confidence)

In the snapshot, the expected type is
`(x: Nat) → x ∈ image.flip.rotate.rows → x ∈ image.rotate.rows`, which is
`Within image.rotate image.flip.rotate` unfolded. Next to it, the actual
type is printed folded and then explained in a `Note`. I suspect the error
is raised after `Within ?b ?c` was opened, by the comparison of the two
unfoldings, and that the expected side is quoted from there. I haven't
confirmed it. **Change:** first find where the expected side is quoted.
If the folded form is still at hand, print it. S to M.

### U6. The design notes don't say (low)

`record-eta.md` §8 and `record-eta-remaining.md:44-50` describe
`same_field_records` and rule 1's "not against blocked" rule, but not the
two SW-1998 rules. Add one sentence each, citing SW-1998. This can go with
the F6 drift fixes from `record-eta-as-merged.md`. S.

### The AoC edits

2020 day 20 (`withinOrientations`) loses the explicit `[b := …] [c := …]`,
and 2021 day 11 (`programRun`) loses `[cavern := cavern]`. No statement
changed, and the SW-1913 comments went with them.

## Details: SW-1995

**Callers.** `rewind_globals` has four callers: `equations.rs:2464` and
`:2469`, and `induct.rs:356` and `:363`. All four run after
`Elaborator::attempt` (`equations.rs:2489-2510`) has called
`budget.restore(saved)`. So they run in whatever operation the declaration
or on-demand request opened. Its steps, limits, stack floor and noted
cancellation are kept, as `forget_since`'s doc says. `generate_equations`
is reached from the definition path (`lib.rs:2745`), and on demand only at
module level (`module.rs:357`, `library.rs:1072`, `:1290`, before a
declaration starts). So `clear_metas` in `rewind_globals` never runs in
the middle of someone else's term. Outside an operation, `forget_since`
leaves the idle budget as it was, which is harmless.

`Kernel::rewind`'s `machine.reset()` also emptied the transparency set.
Only `core/src/check.rs` and `inert.rs` set it, under scope guards that
have already been dropped by the time `rewind_globals` runs. So keeping
the machine loses nothing.

**The test** (`kernel.rs:224-258`) fails on the old code: `reset` puts the
size limit back to `u64::MAX`. That is what SW-1995's report says. **S1
(low):** it checks only `size_limit`. Asserting the stack floor and a noted
cancellation as well would cover the rest of `forget_since`'s contract.
Neither test covers a whole skipped equation either. This fits SW-2090,
which is already about `forget_since`'s tests.

The remaining `Kernel::rewind` callers are `Elaborator::rewind`
(`elab/src/rewind.rs:140`). It is reached from driver sessions and from
`project.rs:166`, `:327` and `:462`, between namespace checks or for a
session rewound after a check. I didn't trace whether `project.rs:166`
can run inside an LSP operation. If it can, a cancellation noted before
it would be cleared there. Medium confidence that it can't: the
operations open per declaration.

## Details: SW-2086

### L1. The blame is worked out outside the catch (medium)

`caught` (`lib.rs:2676-2687`) runs `f` under `catch_unwind`, then, in
`map_err`, calls `self.workspace_of(p)` to find whom to blame. For a path
whose workspace isn't loaded yet (always so for a panic while opening),
`workspace_of` falls through to `home_of` (`:2615`). That calls
`self.source.project(&dir)`, and on disk (`source.rs:65-91`) that means
`project_sources`: it reads and parses `stitchwort.yaml`, then walks the
source folders and reads every `.sw` file.

**Scenario.** A project whose config or folder walk panics: a parser bug
on some YAML, or a file that can't be decoded. Here is what happens.

1. An `Open` goes through `apply`, then `set_text`, `open_workspace` and
   `home_of`, which calls `project`, which panics. The catch takes it.
2. `map_err` calls `workspace_of`, then `home_of`, then `project` again,
   which panics again, now outside any catch.
3. The thread dies, and `keep_checker` takes the `Ok(Err(_)) | Err(_)`
   branch (`:2421`). Checking stops for every project, the `Keeper` is
   lost, and stale diagnostics stay on screen.

That is C1's symptom, through a door SW-2086 opened. Before it,
`workspace_of` used only `find_project`, which checks whether a file
exists. The new test's fault (`load_panics_now`) is injected in
`load_project`, after `home_of`, so it can't see this.

**Change (S).** Work out the key under a nested `catch_unwind`, falling
back to `find_project(parent)` and then the path. Or compute
`workspace_of` before running `f`; that's cheap once L2 is fixed. Test:
inject the fault in `home_of`'s project read.

### L2. `home_of` reads the project's every file (low)

To decide whether one path is a source file, `home_of` asks for the
`ProjectFiles`, which hold every source file's text (`source.rs:22-23`).
It runs:

- once per new workspace, in `open_workspace` (`:3175`), followed by
  `load_project`'s own `source.project`, so the project is read twice;
- in `quarantine_key` for each `open_text` while anything is quarantined,
  which covers every document in `reopen_documents`;
- in `edited`, for every other open file, when a quarantine is lifted.

For the AoC tree that's hundreds of files per call. A broken config is
also logged (`eprintln!`) on every call. **Change (S):** add a
`Source::sources(dir) -> Option<Vec<String>>` that reads only the config,
or keep the answer for the round. Then use it in `home_of`, and in L1's
fallback.

### L3. A doc comment moved onto the wrong function (low)

At `lib.rs:3474`, `relative`'s line "`path` within the folder `dir`,
components joined by `/`" now sits above `sources_hold`'s own doc. So
`sources_hold`'s doc starts with it, and `relative` (`:3485`) has none.
Move the line down. S.

### L4. The C5 test can't fail (low)

`a_file_on_its_own_in_a_project_folder_is_quarantined_by_its_own_key`
clears the fault, then edits, then expects clean diagnostics. On the old
code the same thing happens. The edit doesn't lift the quarantine (wrong
key), but `apply` checks the file anyway, as SW-2087 C5 noted. What does
differ:

- a `Close` of the quarantined loose file then reopening it. The old code
  took the quarantine branch and left `Work::File` in `work`;
- with `checker_panic` left armed for a count, the retry after an edit
  should be quarantined after one restart (one pop-up). On the old code
  the key was cleared, which took two.

Use either. S.

### L5. The `Keeper` is still built after the sessions drop (low)

SW-2087 C1 also asked that the `Keeper` be handed back before the sessions
are dropped. `run` (`:2706-2711`) calls `self.into_keeper()`, which moves
the plain fields out and drops `work` (the sessions) when it returns,
still on the checker thread. A panic in a `Drop` there loses the `Keeper`,
which is the full stop again. Move `work` out first and drop it after the
`Exit` is built, inside a catch. S. This is not ticketed (SW-2091 lists
C6 to C9 only).

### L6. Three copies of the source rule (low)

`sources_hold` is now the single rule for `ProjectWork::holds` and
`home_of`. `MemorySource::project` (`source.rs:194-201`) has its own copy,
which doesn't trim a trailing `/`. So a test project whose config said
`src/` would hold no files in memory, but would on disk if the config
parser didn't normalise it. Use `sources_hold` there too, from a shared
module. S.

### L7. An `Open` lifts a quarantine (low; D3000)

`apply` calls `edited` for `Open` as well as `Change` (`:3040`). The editor
opens files without the user meaning to edit them: a peek, go-to-definition
into another project file, a search result. Each such open lifts the
quarantine and costs a restart. With SW-2089's budget per project, the
damage stays in that project, but it still turns a quarantine into
repeated restarts as someone browses a broken project. Whether only a
change of text counts is Matt's (D2741's word was "edit"). See D3000.

### The SW-2087 findings

| SW-2087 | Status after SW-2086 |
|---|---|
| C1 (reopen outside the catch) | **Fixed** for the main path: `run_caught` starts with `reopen()`, and each document opens under `caught`, so a second panic quarantines. The test can fail. Left: the `Keeper` is built after the sessions drop (L5), and a new uncaught path (L1) |
| C2 (one project spends the session's budget) | **Half fixed.** A retry's first panic quarantines again, at one restart per edit (`edited` keeps the suspicion), and the test can fail. The budget per project is SW-2089 (doing). An `Open` still counts as an edit (L7) |
| C3 (light bulb spends the search budget) | Open: SW-2088 |
| C4 (recorded before sent) | **Fixed** in `publish` (`:2924-2930`) and `show_error` (`:2647-2650`). `forget` removes the entry before sending, which errs the safe way |
| C5 (two ideas of a workspace) | **Fixed**: `workspace_of`, `quarantine_key`, `open_workspace` and `edited` all go through `home_of`. The test can't fail (L4), and `MemorySource` keeps a copy of the rule (L6) |
| C6 to C9 | Open: SW-2091. C7's message now adds "(or reload the window)"; the command it names doesn't exist yet (SW-1980) |
| K1 (`rewind_globals`) | **Fixed** by SW-1995 |
| K2 to K6, N1 | Open: SW-2090 |

## Checked and sound

- **SW-1998.** The unifier can't loop: `Later` is retried only after a new
  solution, and each pass steps the budget. Nothing false gets in: the
  kernel re-checks, and every value built is equal by definition to what
  it replaces. `Value::Call` is built from the spine as `force_call` and
  the read-back expect. Rule 1's `!blocked` guard can't see the new case,
  and the argument loop of `blocked_within` is unchanged. The widening from
  "last is a projection" to "any is" (`?r.f x`) is consistent with the
  stated aim. The `is_folded` narrowing leaves opaque and sealed calls
  (no body seen), gluing off, and over-applied calls as neutrals. Both
  AoC edits only drop explicit arguments.
- **SW-1995.** Every caller is inside the operation, after `attempt`'s
  restore. `forget_since` names every `Kernel` field. No on-demand caller
  sits in the middle of a term, so `clear_metas` is safe. The transparency
  set that `rewind` used to empty is always empty at these points.
- **SW-2086.**
  - `reopen` restores `last` even when it fails.
  - In stopped mode, it forgets every workspace and shows the stop
    message.
  - A quarantined workspace is never loaded by a successor:
    `open_text` checks `quarantine_key` first.
  - A retry keeps its suspicion until the next edit after the one that
    lifted the quarantine. That matches D2741's "panics again before any
    edit".
  - `published` is updated only after each send.
  - The budget test's arithmetic (two restarts for the open, then one per
    edit, so the sixth is one too many) matches the code.
  - `sources_hold` trims as `load_project` trims.
  - The new C1 and C2 tests fail on the old code.
- **The 1 Nov review** (`docs/research/rust-codebase-review.md`). It has no
  finding on `unify.rs` or `rewind_globals`. Its LSP finding, an
  unversioned code-action edit, concerns the search path, not the
  checker. It looks fixed: `document_changes` is negotiated at
  `lsp/src/lib.rs:252` and `:919`. I didn't review it again. Its point
  about scope guards (l. 259) relates to `NO_ETA`, which is set by hand
  (SW-1901/SW-1979). These merges don't touch it.

## Tickets to file

**Lane 1: checker recovery follow-ups (Sonnet, 60 min, `crates/lsp`).**
After SW-2089, which is in the same file. It could be merged with SW-2091.

- L1: work out the blame under its own catch, with a fallback, and test it
  with a fault in reading the project.
- L2: `Source::sources(dir)`, so that `home_of` reads only the config, and
  `open_workspace` stops reading the project twice.
- L5: build the `Keeper` before the sessions drop.
- L3: move the misplaced doc line.
- L4: make the loose-file test able to fail.
- L6: `MemorySource` uses `sources_hold`.
- L7: if D3000 is yes, an `Open` stops lifting a quarantine, with a test.

**Lane 2: SW-1998 tests and notes (Sonnet, 45 min, `crates/elab` tests
and docs only; no unifier logic changes).**

- U2: tests (examples first, then a unit module if cheap) for `blocked_within`'s limits, and for
  `same_field_records` with gluing off.
- U3: a reject example for the `(f x).i` path, and one recording the
  lossy two-field limitation. The brief must ask for `snap:hashes` and the
  `hash_stability` test.
- U1: correct the comment.
- U6: add the two rules to `record-eta.md` §8 and
  `record-eta-remaining.md`.

**Lane 3: the folded expected type in mismatch errors (Sonnet, 30 min,
look first).** U5. Stop at 30 min if the cause isn't found.

**Additions to existing tickets** (orchestrator board edits, no lane):

- SW-2078: U4's correction. Before SW-1998, `blocked_within` and
  `note_unfilled` forced `?r.f` too; start from `first_order` solving an
  unknown whose field already exists.
- SW-2090: S1. Assert the stack floor and a noted cancellation after
  `rewind_globals`, and add one whole skipped-equation test.

## Questions for Matt

- **D3000: should only a change of a file's text retry a quarantined
  project, and not merely opening one of its files?** [rec: yes] Today a
  peek or go-to-definition into a broken project lifts its quarantine
  and costs a restart, so browsing it causes repeated restarts. A
  quarantined file opened would show the quarantine message; the first
  change of text would retry the project.
