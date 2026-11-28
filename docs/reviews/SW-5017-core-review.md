# SW-5017 review: the kernel crate's part of "run until a `?` is reached" (D3777)

**Reviewed:** merge `829d0a8f4` against its first parent, `crates/core`
(`value.rs`, `erase.rs`, `globals.rs`, `budget.rs`, and the two changed
tests), plus the callers that decide what a stop means:
`crates/driver/src/test_run.rs`, `crates/driver/src/run.rs`, the three
`running()` sites in `crates/driver/src/driver.rs` and in
`crates/elab/src/counterexample/mod.rs`.
**Reviewer:** Fable, 28 November 2026. **Method:** paper review only.
Nothing was built or run; every claim below is from reading the code at
`829d0a8f4`. Line numbers are that commit's.

## Verdict

**Sound. Nothing in the core diff changes what the kernel accepts, and I
found no way for a stop at a `?` to be cached or reported as a pass.**

All three new stops are behind `program_running()`, which is false
whenever the kernel checks, and each turns a value the run could not use
(a stuck neutral, or a panic) into an error. An error can only take a
result away. Three small findings, none about soundness, are at the end.

## Q1. Can the new paths run while the kernel is checking? Sound.

**The flag is scoped.** `program` is set in one place,
`Erasure::running()` (`erase.rs:153`), which returns a guard whose `Drop`
puts back both modes (`erase.rs:146`). So it is cleared on an early
return, on `?`, and on a panic that unwinds (`run_relying` catches one,
`test_run.rs:757`; the guard inside `reference_value` drops first).
Nothing forgets or leaks a guard.

**The kernel turns it off, whatever its caller was doing.** The three
places that enter checking call `Erasure::stop()` first:
`in_kernel_modes` (`machine.rs:93`, every admission check),
`KernelModes::enter` (`determined.rs:164`) and `in_own_view`
(`erase.rs:236`, a definition's telescope). The first and third put the
modes back without a guard, so a panic inside leaves `program` false:
the safe direction, and the outer `Running` guard restores it anyway.

**Who sets it.** Ten sites, all outside the kernel, all evaluating a
finished term and then reading the value back:

| Site | What runs under the guard |
|---|---|
| `test_run.rs:724`, `:812` | a test on the reference evaluator |
| `run.rs:408`, `:641` | `main`, simulated or stepped |
| `driver.rs:2143`, `:2165`, `:2307` | a failed test's arm, operand and shown sides |
| `counterexample/mod.rs:874`, `:937`, `:1030` | a counterexample checker and its shown values |

None of these scopes calls the elaborator, unification, conversion on
behalf of a check, `byComputing` or a decision procedure: each is `eval`,
`force`, `quote` and printing. The counterexample search does run during
elaboration, but it is advisory (its module doc: "nothing here makes a
declaration check"), and it maps every error but `Cancelled` to "didn't
finish" (`mod.rs:888`), as it did the stuck value before.

**Unfoldings kept across modes.** A kept unfolding is used only by a
reader in the same modes, `program` among them (`value.rs:310`, `:339`),
so nothing computed in a run is replayed into a check or the reverse.

So during checking an assumption still evaluates to a neutral, a `case`
on it stays stuck, and an impossible branch still leaves the definition
folded (`value.rs:3378`), exactly as `docs/core.md` says.

## Q2. Does `panic!` to `Err(Unreachable)` change what the kernel relies on? Sound.

`branch_asked` already returned `Result`, and a resource error can
already surface at any step, so every caller handles an `Err` here. No
caller treated the panic as "can't happen" except `run_relying`'s
`catch_unwind`, which mapped it to "no result"; the new arm
(`test_run.rs:769`) maps the error to "no result" too.

Nothing is cached after the error:

- `Cache::put` drops every `OutOfResources` outcome (`driver.rs:2053`),
  and `Unreachable` only ever travels as one.
- A kept unfolding is written only for a value that was computed.
- `Erasure::reached` is the one new piece of state. All three sites that
  return `Unreachable` set it on the line before, and nothing else in
  `crates/core` returns `Unreachable`, so a reader straight after the
  error never sees a stale value. Both readers (`test_run.rs:770`,
  `run.rs:623`) follow a run on the core evaluator.

One consequence worth knowing (finding F1): for a test that relies on no
goal, an impossible branch can only mean a compiler or kernel bug. That
used to crash `test`; it is now a test with "no result".

## Q3. Can a test be wrongly cached or wrongly passed? Sound.

**A stop at a `?`** returns before the cache is touched
(`test_run.rs:624-640`): `outcome: Failed`, `hash: None`, never `put`.

**A pass that relied on a data `?` it never reached** is cached, and
that is right. The key (`result_key`, `test_run.rs:349`) hashes the test
with every goal it relies on, and a goal's hash is its label and type,
so filling the `?` changes the key. The pass itself is honest: the
evaluator stops at the first reference to the goal, wherever it is
(`quick` hands it to `eval_step`, `value.rs:2278`, `:2303`; an assumption
has arity 0, so there is no call path that skips this), so a run that
finished never looked at it. And with only data goals every proof was
checked by the kernel with the goal as an unknown constant, so each
holds whatever the `?` turns out to be.

**Under a false proof goal** (D3516, parked) the diff adds no new way to
pass. A test that relies on any goal still runs only through
`run_relying`, on the reference evaluator, and:

- a transport on an erased proof gives no result, as before, and that
  guard is checked on every arm, including the new one;
- an impossible branch, or a `case` on an erased proof of an empty type,
  now gives no result through `Unreachable` rather than through a panic
  or a stuck value;
- a data `?` reached down a path only the false proof opens is reported
  as a stop at that `?`: a failure, which is harmless.

What remains is what SW-2804's review called F1 and this change does not
touch: a false proof goal that steers a run without a transport or an
impossible branch (an assumed `decreasing` goal, say) can still give a
wrong `Bool`. Before D3777 a test that also relied on a data `?` was
refused up front; now it runs, so slightly more tests are exposed to that
existing gap. They are all marked `(assuming …)` by the proof goal.

**Error stand-ins.** A stand-in for data is not an open goal
(`is_open_goal`, `globals.rs:326`), so `unfinished_message` still
refuses the test before it runs (`test_run.rs:255`).

## Q4. Anything else? Nothing weakens the kernel.

- `ResourceError::Unreachable` is a new variant with its own diagnostic
  code, `E-UNREACHABLE`. It is produced only under `program_running()`.
- `Def::is_open_goal` is a read-only accessor.
- The two changed core tests assert the new behaviour and that `reached`
  is `Some(goal)` or `None`. The first one's doc cites D3507 where the
  behaviour is D3777's.

## Findings (none blocks; all from reading, not reproduced)

**F1. A kernel bug's loudest symptom is now quiet in `test`.** Low.
`run_on_reference` (`test_run.rs:735`) turns any error into
`OutOfResources`, so a test that relies on no goal and reaches an
impossible branch reports "no result: it reached code with nothing to
run" among resource failures, where it used to panic. `run` got this
right: `unreachable_diagnostic` says `E-INTERNAL` when the place isn't a
data goal (`run.rs:323`). Suggest the same for tests: when the test
relies on no goal, report `Unreachable` as an internal error.

**F2. "Only a false goal gets here" isn't quite true for the new
empty-`case` stop.** Low, display only. Reading a function value back
evaluates under its binders, where `absurd (lemma x h)` has an erased
theorem call as its scrutinee and no branches. Under `running()` that is
now `Unreachable` (`value.rs:3318`) where it used to stay stuck. Only the
display paths read back under the guard (`driver.rs:2307`, the
counterexample's `shown_value`), and they fall back to "…" or "… (too
large to show)", so no result changes. The comments in `budget.rs:66`
and `erase.rs:57` overclaim slightly, and the fallback text would be
wrong for such a side.

**F3. A test that relies only on data `?`s is still held to the
transport guard.** Low, conservative. Such a test goes through
`run_relying`, where any transport on an erased proof gives "it computes
with a proof, and relies on …" (`test_run.rs:788`). With no proof goal
every proof is checked, so the transport is safe and the test could run;
and `test_assuming` now leaves data goals out (`test_run.rs:337`), so the
message names an empty list of gaps. Suggest skipping the transport
guard when the test relies on no proof or type gap.

## Not covered

The compiled runtimes' handling of a reached `?` (`crates/rt`,
`crates/js`, `crates/native`), `eval` in the elaborator
(`crates/elab/src/lib.rs`), and the CLI's reporting were outside the
brief and were not reviewed beyond the lines cited above.
