# SW-4763 (stage 3 step 1, `check::leave_stated`): Fable review

Reviewed: `lane/SW-4763` at `8440d28dd` (`git diff main...lane/SW-4763`: `crates/core/src/check.rs`,
`globals.rs`, `hash.rs`, `crates/core/tests/it/stated.rs`, `docs/core.md`). 24 Nov 2026.

**Verdict: merge after one small fix (F1), or merge now with F1 as the first thing in step 2.**
Nothing found lets a theorem left stated gain a body, be taken for proved by the kernel, or
make the kernel accept what a one-job check refuses. No caller exists outside the tests, so
nothing here is reachable by a user today. The findings are one panic where the spec promises
a refusal, one sentence of `docs/core.md` that describes a guard nobody has written yet, and
notes for steps 2 to 4.

## Tests run (on the branch, in the lane's worktree, nothing edited)

| Filter | Result |
|---|---|
| `package(stitchwort-core) & binary(it) & test(/^(stated\|trusted\|pending\|hash)::/)` | 22 passed |
| `package(stitchwort-cli) & binary(running) & test(/examples::soundness/)` | 1 passed (the soundness corpus) |

I wrote no new test: the brief says not to edit the lane's worktree. Each finding below is
argued from the code, with line references on the branch.

## Findings, ranked

### F1 (fix; low risk today, a kernel panic on a documented refusal): `register_native` and the pin checks panic on a theorem left stated

`docs/core.md` (new text): "refused afterwards by everything above", where "everything above"
includes "the native registrations refuse it as they refuse an assumption". For a stated
theorem from the cache that is true. For one left stated it is a panic:

- `native::register_native` (`crates/core/src/native.rs:409`) calls
  `pins::check_def(&g.ev(), id, native.builtin())?` **before** `register_shaped`, which holds
  the `def.stated()` refusal (line 434).
- `pins::check_def` → `pins::def_hex` → `hash::def_hash` (`pins.rs:216`, `:285`), and
  `def_hash_in` now asserts `!(def.unproved && mode == Mode::Content)` (`hash.rs:208`).

So `register_native(g, left_stated_id, n)` aborts with "internal error: the full hash of ..."
where the same call on a cache-stated theorem returns `E-BUILTIN`. The same goes for every
other reader of a pin given such an id: `pins::holds`, `pins::stale_def`,
`pins::check_bound_def` (the elaborator's `bind_builtin_def`, `crates/elab/src/lib.rs:4217,
4220`, which stage 2's `admit_stated` calls for a library theorem, `cache/mod.rs:4749`).
`float::register_def` checks `stated()` first and is fine.

Reach today: none (only tests call `leave_stated`). Reach after step 2: only if a pinned
builtin's path is declared as a deferrable theorem, which the design's rule 1 (project
namespaces only) excludes. So this is a fail-closed panic, not a soundness hole, but it is a
kernel entry point that panics on an input the spec says it refuses, and the lane's test
`nothing_gives_a_theorem_left_stated_a_body` doesn't try the natives or `add_validator`.

Fix (about five lines and a test): in `register_native`, refuse `def.stated()` before the pin
check, as `float::register_def` does; and in `pins::def_hex` (or `pins::check`) treat an
unproved theorem as "no hash", which reads there as "not the pinned declaration", the right
fail-closed answer for a pin. Add to the lane's test: `register_native` (pinned) and
`add_validator` on a theorem left stated are `E-BUILTIN` / `E-MALFORMED`.

### F2 (docs, and the main thing for step 3): nothing reads `holds_unproved_theorems`, and the existing stated-theorem assertion doesn't cover a session that reports

`docs/core.md`, new paragraph "A session holding a theorem left stated reports nothing", says
in the present tense that nothing such a session does may be reported or saved, and leans on
"the sessions of commands that use what they load assert they hold none
(`Elaborator::holds_stated_theorems`)". Two things are off:

1. `Kernel::holds_unproved_theorems` has no reader anywhere (`grep` finds only its definition
   and the tests). The kernel provides the mark; no session checks it.
2. `assert_holds_no_stated_theorem` runs only for `Load::Everything`
   (`crates/driver/src/project.rs:348`). A plain `check` session (`Load::Diagnostics`) may
   hold stated theorems by design (stage 2) and **does** print "checked". That is sound for
   cache-stated theorems by invariant W; it would not be for an unproved one. So the one
   session kind that matters most for D3735 has no guard from the existing assertion.

Neither is a defect of this lane's code (no caller), but the paragraph reads as if the
guarantee were in place. Ask: reword it to say the kernel marks the session and that the
driver's assertion is step 3's (SW-4753 chain), and put on step 3's brief: every session that
prints a message, a summary or an exit code, or writes an entry to disk, asserts
`!kernel.holds_unproved_theorems()` whatever its `Load` (the last pass, `check_prepared` for
both loads, the language server, `test`, `run`). It is a three-line assertion and could
equally go in now beside `assert_holds_no_stated_theorem`, unconditional on `load`.

### F3 (low; a pre-existing condition the new doc sentence inherits): "rewinding removes everything checked against it" assumes nothing pending at the mark is defined later

`Kernel::holds_unproved_theorems`'s doc and core.md say a rewind to before the theorem takes
away the mark "with everything that was checked against it". `forget_since` truncates by id.
A definition *declared* before the mark and *defined* after it keeps its id below the mark:

    declare B (pending)         -- id 5
    mark m
    declare T; leave_stated(T)  -- id 6, unproved
    define_group(B, body mentioning T)   -- accepted: T is final
    rewind(m)                   -- T gone, mark gone, B still final, checked against T

This is not new: the same sequence with any `T` leaves `B`'s body pointing at a removed id,
so `forget_since` already relies on its callers never doing it ("Declarations from before the
mark are never changed after they are final" says less than is needed; `mark` is documented
as taken "inside one" declaration by equations, induction and cache replay). I did not audit
the elaborator's rewinds for it (out of this lane's scope). For step 4's review list: confirm
no rewind in a worker can keep a definition finished after the mark, since with unproved
theorems the cost of that old hazard becomes a lost promise mark as well as a dangling id.

### F4 (low): `nat_add::register` takes a theorem left stated as proved

`crates/core/src/nat_add.rs:426` accepts `Nat.addZero` / `Nat.addSucc` when
`state == Final && theorem && assumption.is_none()` and the type fits; a theorem left stated
passes. Neither builtin has a pin, so no hash is asked for. The module says the rules are
sound by the argument about the pinned `Nat.add`, not by these proofs, which are "a safety
net against binding the rules to the wrong definition"; the net is only checking the type,
and the type is checked. So nothing unsound, and rule 1 keeps the prelude out of deferral.
Suggest `&& !def.unproved` there anyway, so that "a theorem that isn't an assumption" keeps
meaning "proved by this build".

### F5 (low, pre-existing from SW-4734): a stated theorem's proofless hash panics if `proof_positions` runs out of resources

`def_hash_in`'s `def.stated && mode == Proofless` branch calls `Hasher::declaration`, which
takes the statement-only path only when `proof_result(id)` is true. `erase::proof_positions`
returns `result: false` when its telescope runs out of budget (`erase.rs:284-292`), and
`declaration` then does `def.body.expect("internal error: hashing a definition that isn't
final")`. For a proved theorem the fallback hashes the body; for a stated one there is none.
The kernel already knows the answer (`def.proof`, checked by both makers), so the stated
branch can write `proof-def`, `theorem`, the type itself without asking `proof_positions`.
Same for both kinds of stated theorem; file as a follow-up, not this lane's.

### F6 (note): the assertion sits after the cache lookup, and the cache is a public field

`def_hash_in` returns a cached hash before reaching the new assertion, and
`Kernel.caches.hashes` is `pub` (stage 2's `admit_stated` seeds it, `cache/mod.rs:4746`). So
"asking is an internal error" holds unless a caller seeds a full hash for the id first. That
is the elaborator's trust, as it is for stage 2. For step 2's brief: the interface entry's
admission must not seed `caches.hashes` for a deferred theorem (the design says so; this is
where it would silently stop being true).

### F7 (comments left behind)

Three doc comments still say every stated theorem was proved where it was made:

- `Def::defined` (`globals.rs:341`): "or a stated theorem, whose proof was checked where it
  was made".
- `hash::has_interface` (`hash.rs:250`): the same phrase.
- `assumption::mentions` (`assumption.rs:142-150`): "That is true only because it is made
  from a cache entry ... (invariant W)". For one left stated it is the promise; core.md's
  "Reliance" paragraph was updated, this comment wasn't.

## The brief's questions

**(a) Given a body, or treated as proved?** No. Every writer of `state`, `body`, `stated`
and `unproved` in `crates/core/src` (I listed them: `install_group`, `leave_stated`,
`assume`, `admit_trusted_stated`, `abandon_pending`, the `Delay` and Float primitive
registrations, and two `test-bypass` helpers) either requires `State::Pending` or makes a new
definition. `leave_stated` makes it `Final`, so `define_group`, `admit_trusted_group`,
`retype_def`, the primitive registrations and the `mark_*`/`set_unfolding` functions all
refuse or ignore it; `set_run_body`, `admit_trusted_run_body` and `add_validator` refuse
`stated`. Nothing clears `unproved`. A group submitted with it as a member fails the other
members and leaves it alone. "Treated as proved" is the design (D3735) for checking; the
places that mean "proved by this build" are F1 (panic, not acceptance) and F4.

**(b) Saved entry, report, `axioms`/audit, run, native, validator?** Every guard keys on
`stated`, which `unproved` implies: the encoder, `walked_body` (`axioms.rs:226`), the
runtimes, `run_body_shape`, `add_validator`, `register_shaped`, `float::register_def`. The
gap is F2: a session that reports. Natives: F1.

**(c) Past a rewind, or across sessions?** The mark is a field of the definition, so
truncation removes exactly it; caches are cut by id (`caches.rs:40`). `Kernel` and `Def` are
`Clone`, which copies the flag. Subject to F3. Across sessions the kernel has no channel;
that is the interface entry's record in step 2 (it must carry "unproved" so the admitting
session marks itself too; `admit_trusted_stated` as it stands would launder the mark, so the
interface entry needs its own admission, as the design says).

**(d) Different interface or proofless hash from the proved theorem?** No. After
`leave_stated` the definition has the fields `admit_trusted_stated` produces: arity 0, no
group, default `transparent`, `lift_leaf` false, `recursive` false (a pending definition
can't have had them set and stayed pending: `install_group` ends in `Final` or `Failed`),
the declared type and the kernel's proof mark. `interface_hash` reads the type only;
the proofless branch reads the type and `theorem`. `proof_positions` and `of_def` don't
remember an answer for a pending definition, and reliance memoises only final ones, so
nothing cached while it was pending is stale after. The lane's test compares the theorem's
interface and proofless hashes and its users' full and proofless hashes across proved (two
proof shapes), cache-stated and left-stated: equal.

**(e) Is the new panic reachable from ordinary use?** Not today. Through the kernel's own
API: F1. After step 2, the callers that will hit it in a worker unless they are kept away:
`driver/src/declhash.rs:140` and `live/trial.rs:570` (hash every definition), the cache
encoder's `def_hash` of a namespace's own definitions (`cache/mod.rs:2971, 4273`),
`rt/src/natives.rs:223`, and the pin readers. A panic rather than `None` is the right
choice for those (SW-4744), and step 3 already plans a worker-panic test.

**(f) Accepts anything a one-job check wouldn't?** Not in the kernel's rules: it adds a
constant of a type the kernel checked in this session, which is the promise D3735 allows, and
no rule reads its absent proof (rule F seals a proved one as well). `leave_stated` refuses
what `define_group` would have refused about the statement (a failed dependency). What a
one-job check also establishes, and this doesn't, is the proof and its reliance on goals;
both are the last pass's and the key chain's job (design §5), outside this lane.

**Is `trusted_type` sound, and does `retype_def` matter?** Sound, and conservative. It is
set only by `admit_trusted_def`, never cleared, not hashed, and not in the cache dump
(`cache/dump.rs` names its fields; `Def` has no `Debug`), so no checked-against-replayed
comparison sees it. `retype_def` on a declared theorem re-checks the type as `declare_def`
does (sort, proof mark), so the flag rightly stays false. `retype_def` on a trusted one
checks the new type but leaves the flag set, so `leave_stated` refuses a theorem it could
take: stricter than needed, harmless, and the caller falls back to checking the proof. What
the flag buys is that `admit_trusted_def` + `leave_stated` can't make a theorem with neither
its statement nor its proof checked here; that would be no worse than what the cache's trust
boundary already allows, so it is defence in depth, worth keeping.

**Is `docs/core.md` accurate?** The preconditions, the result and the hash sentences match
the code. Inaccurate or ahead of the code: "refused afterwards by everything above" for
natives (F1), and the "reports nothing" paragraph (F2). "The mark ... removes it with
everything checked against it" holds under F3's condition.

## For the later steps' briefs

- Step 2: the interface entry's admission marks the admitting session (a second maker of
  `unproved`, or `leave_stated`'s twin on the trust boundary), and seeds no full hash (F6).
- Step 3: the unconditional `!holds_unproved_theorems()` assertion at every reporting and
  disk-writing session (F2).
- Step 4: worker rewinds against F3; the full-hash callers listed under (e).
