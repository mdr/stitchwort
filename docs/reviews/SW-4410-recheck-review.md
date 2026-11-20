# SW-4450: review of lane/SW-4410, carried-over check cache stage 2 (the kernel re-check)

Fable paper review, 20 November 2026. Branch `lane/SW-4410` at `2d4dfc309`
(three commits), read with `git diff main...lane/SW-4410` and `git show`.
Nothing was built or run. Line numbers are in the lane's files.

## Verdict

**Merge after named fixes** (M1 to M3).

Within the session that does it, the re-check is sound: every definition
and data type of a re-checked entry enters the kernel through the same
calls elaboration uses, and I found nothing it installs unchecked. The
problem is the step after: a re-checked entry is saved again under this
kernel's stamp with the bytes the other kernel wrote, and those bytes hold
two things the kernel derives, which the re-check works out again but never
compares with the entry. The next session's trusted replay installs the
other kernel's values (M1). The fix is a few lines.

## Must fix before merge

**M1. A re-checked entry is kept with the other kernel's field sorts and
erasure flags, which the next session installs unchecked.**
`crates/elab/src/cache/mod.rs:3333-3361` (the checked data branch of
`submit`), with `keep_rechecked` at `:1680` and its two callers.

- The checked branch passes `define_data_group` only the fields, result,
  `implicit` and `braced`; the kernel works out `field_sorts` and
  `field_erased` itself (`crates/core/src/check.rs:3641-3644`: the sort
  `check_type` gives, and `is_type_former`). The entry's own
  `c.field_sorts` and `c.field_erased` are not read on this path, and not
  compared with what the kernel computed.
- The content hash doesn't cover either (no mention in
  `crates/core/src/hash.rs`; stage 1's review said so in its F2), so
  `hashes_as_recorded` can't see a difference.
- `keep_rechecked` then writes the same body again, stamped with this
  build's kernel side. The next carrying session finds it as this build's
  own non-exact entry, `usable` gives `recheck: false`, and
  `admit_trusted_data_group` installs the entry's `field_sorts` and
  `field_erased` as written, checking only their lengths
  (`check.rs:3912`).
- Both are read by the checker, not only by the runtimes:
  `value::proof_field` (`value.rs:4449`: conversion skips a field whose
  sort is `Prop`), the subsingleton test for eliminating a proposition into
  data (`check.rs:1318-1321`), record eta (`check.rs:3169`), and
  termination's "relevant" parts (`termination.rs:622`, `:801`).

*Failure scenario.* Kernel side A gives some field type the sort `Prop`;
kernel side B, after a universe fix or any change to sort inference, gives
the same term `Type`. A wrote an entry for `type Box = MkBox (x: T)` with
`field_sorts = [Prop]`. Build B carries it over: `define_data_group`
accepts the type (computing `[Type]`), the hashes match, the entry is kept
as B's. The session after that replays it trusted, and kernel B now holds
`Box` with a data field marked as a proof. Conversion skips it, so
`MkBox a = MkBox b` holds by `rfl` for any `a`, `b`, and `False` follows in
any namespace elaborated in that session. The same shape with
`field_erased` (a change to `is_type_former`) gives B's termination
checker A's flags. This is exactly the case stage 2 exists for ("sound
whatever changed in the kernel", §4.2), and it is new with this lane:
stage 1 only trusted entries from an identical kernel side, whose derived
fields are this kernel's by construction.

It also weakens `--recheck` as an audit: an exact entry with wrong field
sorts (a codec slip, a damaged file) passes `--recheck` and is then
installed by the trusted replay, so "a refusal is a finding: the trusted
replay would have admitted it" doesn't cover this part of the entry.

*Fix.* In the checked data branch, after `define_data_group` succeeds,
compare each constructor's `field_sorts` and `field_erased` as the kernel
now holds them with the entry's, and refuse on a difference ("a data
type's field sorts came out differently"). Then a kept entry holds only
what this kernel derived, and `--recheck` vouches for everything the
trusted replay takes from a data entry. (The alternative, encoding the
entry again from the kernel's state before keeping it, is more code for
the same result.)

**M2. Tests for M1 and for the kept entry.**
`crates/elab/src/cache/mod.rs` tests and
`crates/driver/tests/projects/check_cache.rs:2001`.

- A unit test beside the forged-proof one: a `DataEntry` with one `Nat`
  field recorded as `Sort::Prop` (and one with a wrong `field_erased`).
  The trusted admission installs it; the re-check refuses and undoes it
  (`datas` count back, `refused_on_recheck == 1`). It fails before M1's
  fix.
- In `a_kernel_side_change_has_a_carried_entry_checked_again`, the `kept`
  run asserts only counts. Assert `kept.dump == fresh.dump` too: the kept
  entry's trusted replay is the path M1 is about and nothing compares its
  result with a fresh check's.

**M3. `docs/core.md:557` says more than the code does, and leaves out what
the next session trusts.**
- "so types, bodies, termination, universes and positivity are this
  kernel's verdict" is right for the re-checking session. The next
  sentence, "It is then kept as this build's own (not exact), so the next
  session carries it over without the re-check", needs the condition that
  makes it sound: what is kept is the entry as written, so everything the
  trusted replay takes from it must have been compared with what this
  kernel produced: the terms through their hashes, and (after M1) the
  field sorts and erasure flags directly. Say so, and say that run bodies
  are type-checked but not compared (they never unfold in the kernel).
- The re-check trusts the entry's side tables, names and marks exactly as
  a trusted replay does (the elaborator's side). The text should say the
  re-check covers the kernel's verdict only; the doc comment at
  `cache/mod.rs:3064`, "so this path trusts nothing in the entry", has the
  same overstatement.
- The sentence defining a carried-over hit still reads "needs the same key
  and the same kernel-side fingerprint ... accepted by a kernel identical
  to this one". With kept entries the stamp's kernel side now means
  "accepted by this kernel side, when written or on a re-check"; one
  clause fixes it.
- `check --recheck`: add that a plain `check` then leaves no namespace out
  (it is in the proposal's "As built" and the flag's help, not in the
  spec), and that it covers the entries the session loads, not the whole
  cache folder.

## The six questions

**1. Can a re-checked entry install anything the checking calls didn't
check? Not in the re-checking session.** Item by item, trusted path
against checked path:

| Item | Trusted replay | Re-check |
|---|---|---|
| Definition's type, theorem flag | installed as written (`admit_trusted_def`) | `declare_def`: type checked, a theorem's type must be a proposition; export off on both |
| Body, arity, group, transparency set, `recursive` | body as written; the rest computed by `install_group` | `define_group`: typed, termination for the group, `unfolding` list checked; the rest computed the same way |
| Run body | as written, shape only | `set_run_body`: shape and type |
| Data declaration (params, sort, indices, record) | as written, structural checks | `declare_indexed_data_group` |
| Constructors | as written, with the entry's `field_sorts` and `field_erased` | `define_data_group`: types, universes, positivity; sorts and erasure computed (not compared: M1) |
| Marks (`fold`, `instance`, `opaque`, `tailrec`, parameter default, `unfolding`, auto parameters, `no_eta`) | set on the pending declaration | the same calls, the same moment; these are what the kernel takes from an untrusted elaborator anyway, and the ones that affect meaning are hashed or checked in `define_group` |
| Built-in bindings | `bind_builtin_*` for a library file, compared with the entry's `bound` | the same, after the lane's second commit |
| Final marks, order | each group as soon as its needs are final | the same loop |
| Hashes | seeded from the entry (compared if carried) | always compared before seeding, exact entries too |
| Names, paths | `module_of`, path compared after declaring | the same |
| Side tables: instances, walk lemmas, equations, `%` helpers, scope, navigation | `replay_tables` | the same: trusted as the elaborator's side on both paths; none of it reaches the kernel's verdict except through terms the kernel then checks |

Exports, validators, primitives, core built-ins and declarations without a
body (open goals' assumptions) never reach an entry (`encode`, `:1800`
on), so there is no checked-path counterpart missing for them. Defining a
group earlier than the elaborator did only ever checks it in a state where
more is final, each state one the kernel reached by its own checks. A
library file loaded part way through another declaration is checked in the
kernel's own modes (`in_kernel_modes`), as elaborating it there would be.

**2. Is keeping a re-checked entry under this build sound? Not as built:
M1.** With M1 fixed, yes. The next session's argument needs: these terms
were accepted by this kernel side, under this key's modes and limits, over
dependencies with these content hashes. The re-check gives that for the
terms as submitted; the hash comparison ties the terms the kernel gave
back to the recorded hashes; and the next session's decode self-check
(run for every non-exact entry) hashes the entry's own terms again before
seeding. Run bodies are the one remaining difference between what was
checked-and-installed and what is kept (F1); they can't affect a proof.

**3. Is the undo complete? Yes.** Every refusal in `submit`, the built-in
comparison and the hash comparison returns through the one error arm of
`admit_replayed`, which calls `forget_since` and truncates the session's
owners and paths. `forget_since` cuts the environment, the built-in
bindings and all five derived caches by id (`caches.rs:38`); the checking
calls write nowhere else that outlives an operation (the machine holds
only the budget, modes and `apart_sets`). A group `define_group` refuses
is marked failed and then removed with the rest. In dev and test builds
the undo witness asserts this. A refused carried namespace taints the
session (`namespace_carried_late`), as stage 1's M1 requires. I found no
way for part of a group to survive.

**4. Does `--recheck` trust nothing? For the kernel's verdict in that
session, yes; nothing bypasses it.** Every replay goes through
`cache_read` and `usable`, which sets `recheck` on every hit, library
files and the files a namespace's replay loads included. `plan_namespace`
returns `None`, so no namespace is reported from its entry unloaded. The
bundle stores are the playground's and go through the same two functions.
Limits of the claim: it re-checks what the session loads (a
`check Ns --recheck` leaves other namespaces' entries alone, and library
files nothing needs); it says nothing about the entry's field sorts and
erasure until M1; and with no cache folder, `--expand` or an empty cache
it prints nothing at all (F3).

**5. Is the `docs/core.md` text correct and complete? Mostly correct,
incomplete: M3.**

**6. Are the tests enough? No.** The forged-proof test is right (the body
`fun P => P` is not a proof of `(P: Prop) -> P`; the trusted path installs
it, the re-check refuses and undoes it, and the counters are told apart),
but it is one definition in a namespace entry. Must: M2. The rest: F2.

## Follow-ups (tickets, not blockers)

- **F1. Compare run bodies on a re-check.** `set_run_body` installs the
  term `check` gives back; the kept entry holds the one submitted, which
  nothing hashes. Compare them and refuse on a difference, so a kept entry
  is in every part what this kernel installed. Behaviour only, never a
  proof.
- **F2. More tests.**
  - A refusal part way through an entry: several definitions and a data
    type, the last refused; assert the earlier ones and the type are gone.
    Today's test has one definition.
  - Data on the checked path: a non-positive type and a non-terminating
    group, each admitted by the trusted path and refused on a re-check.
    The lane's one bug was in this branch and was found by the
    measurement, not a test.
  - A library entry with built-ins bound, refused on a re-check: the
    bindings are undone.
  - End to end: a carried entry this kernel refuses (the
    `refuse_replays_after` hook will do): the unit is elaborated, the dump
    equals a fresh check's, `refused_on_recheck == 1`, and what the
    session writes is not exact.
  - `check_cache.rs:1993` asserts `rechecked == hits` for library files
    without asserting `hits > 0`; if the project's library files aren't
    cacheable in that harness, the library branch isn't exercised.
  - Both kinds of candidate present: the one this kernel side accepted is
    preferred, and with `--recheck` it is checked again.
  - The CLI's `checked again by this kernel` line, and that `check
    --recheck` of a project reports no namespace from its entry.
- **F3. `--recheck` should always say what it did.** With nothing
  re-checked (no cache folder, an empty cache, `--expand`),
  `rechecked_units` is `None` and the run looks like a pass of the audit.
  Print "checked again by this kernel: nothing" when the flag is set.
- **F4. Wording.** `cache/mod.rs:3064` "trusts nothing in the entry" should
  read "trusts nothing in the entry for the kernel's verdict"; the side
  tables and marks are taken as written.
- **F5. Stage 1's F2 is now half done by M1.** The same comparison could
  run for carried entries on the trusted path (recompute and compare the
  field sorts), which would close the forgotten-`FORMAT`-bump case there
  too; it costs a `check_type` per field.

## What I did not check

Nothing was run. I took the hash's coverage of terms, flags and data
shapes from stage 1's review and a grep of `hash.rs` for the two derived
fields; I did not re-read `hash.rs` in full. I did not read `decode`'s
dependency comparison again (unchanged by this lane), `replay_tables`
beyond its outline, or the LSP's use of the new counters. Whether
`List.length`'s run body (`length_run_body` in `bind_builtin_def`) can
collide with the entry's own run body on replay is older than this lane
and the same on both paths; I did not chase it.
