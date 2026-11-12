# SW-2977 review: the Bool reader (stage 2)

Independent Opus review, 12 Nov 2026, of `lane/SW-2977` (Bool as a
proposition, stage 2; docs/proposals/bool-as-proposition.md, D3487, D3488,
D3531). Read-only, with probes against the lane's release binary.

**Verdict: merge after fixes.** Every use of a reading goes through the
reading theorem (`Iff.forward (r args) h`, `Iff.backward (r args) p`, or the
`¬e` term from `Bool.falseNotTrue`), and the kernel checks it all. No way
found to prove something false or to change a program that checks today.

## High

- **H1. Panic on a reading whose test has a non-parameter argument**
  (confirmed). `reading.rs:235` prints the test for `E-READING-SHAPE` in a
  context with no binders; `small (n + 1) ↔ n < 9` (or `f n n`) panics at
  `pretty.rs:723`. Also reached by `STITCHWORT_GLUE=0` on
  `examples/accept/bool-readings.sw`. Fix: print with the theorem's
  parameters bound; add a reject example.

## Medium

- **M1. Field access through a reading has no bound and hides other errors**
  (confirmed). `dot.rs:433-438` re-reads on any `Err`: a reading `f n ↔ f n`
  recurses to `E-RESOURCE`; a failed receiver's or opaque `.unfold`'s error is
  replaced. The docs say one layer. Fix: read once, only on "no such field".
- **M2. User readings fail unglued** (`STITCHWORT_GLUE=0`): `reading_info`
  and `lookup` take the test's function from values, which unfold. Fix: take
  it from the elaborated term.
- **M3. Patterns don't read again** though §6.4 says so: `Inl`/`Inr` on
  `Bool.not (a && b) = True` is `E-NO-READING`. Fix: loop the reader
  (bounded) or change the note. Also §5.7 (six call sites, not three) and
  §5.6 (a folded call is looked up by its function first) are out of date.

## Low

- **L1.** A use before the reading in the same file gets `E-NO-READING`
  saying to declare one; a reading whose proof fails cascades
  `E-NO-READING` to its users.
- **L2.** A reading on an alias (`tiny := small`) is filed under `small`, and
  the overlap message names `small`.
- **L3.** Nested backticks in "with `a constructor of `Or``"; `for_ctor`'s note
  says "matches" when building.
- **L4.** Unguarded indexing at `reading.rs:363` and `reading_info`'s
  `slots[l]` (believed unreachable).
- **L5.** `.read` is checked before member lookup, so a project's own
  `Eq.read` would be shadowed; `h.read` on `?e = True` fails instead of
  waiting.

## Checked and fine

- Readings found by unfolding are applied to the unfolded test's arguments;
  the kernel accepts the match by unfolding. `&&`/`||` readings applied
  through `()` branches are kernel-checked. No universe levels involved.
- The lane's flagged one-level shift in field types only feeds choices on
  the outermost data type (which type a pattern matches, unit/empty,
  `E-NOT-EMPTY`); `check_tree` takes real types from `cx.types`.
- Every new entry point runs only where the old code failed (new
  `Value::Eq` arms in `check_value`, the error branch of `check_tree`,
  test-fact substitution in `field_types`/`records.rs`, the field-access
  fallback). Recommend the full hash snapshots after merging.
- One reading per test: `E-READING-PLACE` forces the reading into its
  function's unit, where `E-READING-OVERLAP` catches a second. Rewinds undo
  readings; the cache replays them with their unit; the key chains source
  text and dependencies, so editing a reading re-checks its users.
- Unfolding is deterministic and bounded (9 lookups, never `opaque`, not a
  definition stuck on its arguments); it ignores visibility, as the note
  accepts.
- `Iff` moved into the core with its hash lines unchanged; a program's own
  `type Iff` still checks; the `¬e` term is correct.

Disposition (orchestrator, 12 Nov 2026): H1, M1, M2, M3 (make patterns read
again, bounded) and L1-L4 sent back to the lane; L5 left.
