# SW-1782: a call's kept unfolding records the modes it was made in

**Ticket:** SW-1782 (from SW-1748; SW-1784's likely cause). **Decision:** D2570
(Matt, 7 Nov 2026): cached unfoldings record the mode they were computed in
(gluing, the transparency set, erasure); one made with gluing on can be read with
gluing off, not the reverse. This is step 1 of
[closed-type-values.md](../proposals/closed-type-values.md) §4. **Lane:** Opus,
`lane/SW-1782`.

## Summary

- **Cause, confirmed:** a glued call (`Value::Call`) keeps its unfolding in a cell
  shared by every copy. The cell was reused whatever mode the reader was in. A
  call forced first with gluing off kept an unfolding with no calls left in it. A
  later folded read-back (`quote_folded`, with gluing on) that forced the same
  call took that value and wrote it out in full, where a glued unfolding would
  have kept the inner calls as calls. So what the elaborator wrote depended on
  whether something had forced the call unglued first.
- **Fix:** the cell records the epoch and the modes (`value.rs`, `Kept`, `Modes`).
  `Unfolding::get` uses it only if the reader could have computed it:
  same erasure flags, same transparency set, and gluing on when it was made or off
  in the reader. Otherwise the reader computes the unfolding again and its own
  value replaces the old one.
- **Evidence:** with an instrumentation that forces every call unglued before each
  folded read-back, 317 declaration hashes moved in the std + rogue dump without
  the fix (286 in std, 31 in `Rogue.Proofs`). With the fix, none move. Without the
  instrumentation, the fix moves no hash.

## 1. Reproducing it

The instrumentation (kept, behind an environment variable, in `value.rs`): with
`STITCHWORT_DEBUG_FORCE_UNGLUED` set, `quote_folded` with gluing on first reads the
value back unfolded with gluing off (`quote`), inside a budget attempt whose
steps and errors are thrown away. That forces every call it reaches, unglued,
filling their cells, and then the folded read-back runs as usual. It is a
stronger form of SW-1748's (an unfolded read-back of each value, both evaluated
unglued and compared by conversion), standing for any unglued forcing that
happens to come first: `decide` (`auto.rs`, `decide_unglued`), a mention test, a
conversion with gluing off.

The dump is `hash_stability`'s `dump` (`docs/testing.md`, "Hash dumps"):
std and `games/rogue` elaborated from source, so with no check cache.

| build | dump lines | moved vs. base | of them `Rogue.Proofs` | time |
|---|---|---|---|---|
| base (`main` at 142580fd7) | 6,671 | | | 14.8 s |
| base, instrumented | 6,671 | 317 | 31 | 38.3 s |
| fix | 6,671 | 0 | 0 | 15.6 s |
| fix, instrumented | 6,671 | 0 | 0 | 38.3 s |

The moved std lines are in `Std.Map` (68), `Std.Parse` (64), `Std.Set` (54),
`Std.Graph` (52), `Std.List` (28), `Std.NonEmptyList` (12), `Std.Text` (5) and
`Std.Nat` (3). SW-1748 saw 12 `Rogue.Proofs` hashes move and
`resolveOnFloor.%match3`'s type grow from 1,144 to 54,784 nodes; this
instrumentation moves its hash but not its size (1,144 either way). The two
instrumentations force different calls first, so the classes overlap but aren't
the same; the mechanism is.

## 2. The cause, precisely

`force_call` (`value.rs`) unfolds a call and `Frame::Unfolded` keeps the result
in the call's `Rc<Unfolding>`. `Unfolding::get` checked only the metavariable
epoch. A call forced with gluing off evaluates its body unglued, so every call it
makes is unfolded at once and the kept value has none left. The folded read-back
forces a call that steps at once (`matches_at_once`) and writes what the force
returns, reading the calls in it back as calls. Given the unglued value, it
writes their unfoldings instead.

A concrete instance, `Std.Text.stripPrefixSome`'s `%match1` (std,
`Text/Text.sw:458`):

```
| Some chars =>
    Text.ext text (Text.append prefix rest)
      (rewrite Text.stripPrefixCharsForward _ _ found, Eq.sym (Option.someInjective h) in rfl)
```

`h : Text.stripPrefix text prefix = Some rest`, and with `found`, `stripPrefix`
steps to `Option.map Text.fromList (Some chars)`, then `Some (Text.fromList
chars)`. Glued, `Text.fromList chars` stays a call, and the implicit arguments of
`Eq.sym` and `Option.someInjective` are written `Text.fromList chars` (three
places). With the call forced unglued first, they're written `MkText chars`,
`Text`'s constructor, which is what `fromList` computes. The term is 182 nodes
instead of 185, so the hash moves; the two terms are convertible.

Which readers took a cell made in another mode (an analysis build, not
committed, counting the times a reader with gluing on was handed a cell made
with gluing off, with the instrumentation on, std + rogue):

| reader | reads |
|---|---|
| inside a folded read-back | 16,121 |
| elsewhere (unification, conversion, `force` from elaborator code) | 23,068 |

The most frequent calls were `Std.Parse.%res`, `Std.List.Mem`,
`Std.Parse.State.at`, `Std.Effect.PlusRes`, `Std.Not` and `Std.Bool.ifThenElse`.
Both kinds matter: a unifier that solves a metavariable from an unglued unfolding
puts the full value into the solution, which is written out later.

**In normal runs** (no instrumentation), the same count over std + rogue is 4,
all `Std.Effect.CompD` in the "elsewhere" class, and none of the four changes a
hash. No reader was handed a cell made under another transparency set or
erasure mode. So today the order-dependence is latent: it shows only where some
code forces a call unglued before a folded read-back of the same value, which is
what SW-1748's instrumentation did, and what a later change (stage 6b's match
motives, a new `decide` site) could do for real.

Not the cause: running out of budget. SW-1784 named it as a second possible
source (39 of SW-1748's conversions ran out). Here the instrumentation's work runs
in its own attempt and its errors are dropped, and with the fix it moves nothing,
so the hash moves come from the shared cells alone.

## 3. The fix

`Unfolding` holds `Option<Kept>`, and `Kept` is the epoch, the value, and
`Modes`:

- `glue`: `Machine::glue`;
- `erasing`: `Erasure::active`;
- `program`: `Erasure::program_running` (opaque bodies are visible while a
  program runs, `hidden`);
- `transparent`: the transparency set (`Rc<[DefId]>`, the same `Rc` the machine
  holds, so recording it is a reference count).

`Kept::fits` is the rule: the epoch as before (0, or the reader's), erasure
flags equal, the transparency set equal (pointer first, then contents), and
`m.glue || !reader.glue`. A reader for which the cell doesn't fit runs the
unfolding and `set` overwrites the cell, so a cell holds one value at a time.

**Why glued serves unglued.** A glued unfolding differs from the unglued one only
by having calls where the unglued one has their unfoldings. An unglued reader
meets those calls through `force`, which is true of every call
(`needs_forcing`), so it computes what it would have computed; and `quote`
unfolds every call it reads. Cells were already read this way before the
fix (SW-1786's review of fix 3, `interfaces::locals`, relies on it). The reverse
doesn't hold, which is the bug.

**What it can't do.** It only refuses a kept value; it never makes one up. So it
can't make the kernel accept anything it wouldn't with no cache at all. A mode
the key missed would be the remaining risk: these are the three that
`unfold_now` reads (`hidden` reads the transparency set and `program_running`,
`erases_result` and `erased_arg` read `active`, the gluing branch reads `glue`);
the budget is not a mode (it can only stop an unfolding, which is then not
kept).

**Modes at `set`.** The modes are read when the unfolding is stored, at the end
of its force. Modes are set by guards outside the machine, so they're the same at
the start and end of one `run`.

## 4. Cost

- **Memory.** A cell grows by the transparency set's fat pointer and three
  flags (24 bytes), on the heap allocation every call already has. `Value`'s size
  is unchanged.
- **Recomputation.** Only where a cell made in another mode is read: 4 times over
  std + rogue in a normal run (above).
- **Time.** The rogue dump: 14.8 s before, 15.6 s after, one run each on a loaded
  machine (noise at this size). Bench counts: §6.

## 5. Tests

- `crates/core/tests/it/glue.rs`, three new tests, each failing with the old rule
  (checked by putting it back):
  - `a_call_forced_unglued_reads_back_folded_as_if_never_forced`: `outer (Succ x)`
    reads back folded as `Succ (twice x)` whether or not it was first read back
    unglued (before: `Succ (Succ (Succ (double x)))`).
  - `an_unfolding_computed_glued_serves_an_unglued_reader`: the relaxation, and
    that an unglued cell is computed again for a glued reader.
  - `an_unfolding_that_saw_an_opaque_body_isnt_used_once_it_is_hidden`: a cell
    filled with an opaque definition in the transparency set, or while a program
    runs (erasing, and with erasure turned off, so the program flag is tested on
    its own), isn't handed back once the definition is hidden.
- The rogue dump with and without the instrumentation (§1).
- The others the brief lists: §6.

No driver test runs the instrumentation: its switch is read once per process
from the environment, and elaborating std for a test costs about 13 s. The core
tests pin the rule; the instrumentation is for checking a whole project by hand,
as `docs/testing.md` now says.

## 6. Results

| check | result |
|---|---|
| `glue::` (core `it`, 11 tests, 3 new) | pass; the 3 new ones fail with the old rule |
| rogue dump, instrumented vs. not, with the fix | identical (6,671 lines) |
| rogue dump, fix vs. base | identical |
| `hash_stability` `prelude`, `examples`, `projects`, `a_namespace_checked_alone_has_the_same_hashes` | 5/5 pass (default sample) |
| `task test:affected` (selection estimated 71 s; ran 142 s beside the bench) | 832/832 pass |
| `cargo clippy -p stitchwort-core --all-targets`, `cargo fmt` | clean |

**Bench, base and fix on the same tree, counts only** (`task bench -- --no-time`;
the committed baseline predates both, so both runs differ from it alike):

| benchmark | base | fix |
|---|---|---|
| `examples` steps | 6,480,039,232 | 6,480,040,412 (+1,180) |
| `examples` allocations | 7,029,423,514 | 7,029,423,988 (+474) |
| `examples` peak heap | 1303.7 MB | 1303.7 MB |
| `check-number-dependent` peak heap | 466 kB | 469 kB |
| every other benchmark | | the same counts |

So over the 1,498 examples the rule recomputes a handful of unfoldings
(1,180 steps in 6.5 billion), and memory is unchanged at this precision.

## 7. Not done, and what's next

- **Whole AoC** wasn't run (it needs Matt's OK). The std + aoc hash dump, base
  against fix (about 45 s each, `docs/testing.md`), is the check that would
  show whether any AoC proof's written terms depended on a cell's history
  today; rogue and std say they don't.
- **Steps still depend on history** wherever cells are shared, as before: a
  cell that fits is reused. closed-type-values.md's option 3 keeps the kernel off
  kept cells for that reason; this lane doesn't change it.
- Next: closed-type-values.md §4 steps 2 and 3 (a glued `Def::ty_value`, the
  kernel evaluating statements afresh), which rely on this rule for the
  elaborator's, programs' and tools' reads of a session-long glued value.
