# SW-4703 review: removing the `Nat.equalRefl` / `Nat.equalSound` natives

Reviewer: Fable, 24 Nov 2026. Reviewed: commit 8066a6aa4 on `lane/SW-4703`
against merge base bb547bcf2. Paper review plus small probes with the lane's
release binary (confirmed to be the changed build: it has no `EqNatRefl`
string, main's has one).

## Verdict

Sound to merge. The two natives were dead code in every shipped path, and
removing them changes nothing the kernel accepts, no hash, and no checking
cost. One thing is left for the verifier (finding 1) and one stale document
(finding 2). No blocking findings.

## Findings

1. **Low, unverified by any run: the erasure-off comparison tests are the one
   place the natives still fired.** With `Erasure::set_disabled(true)` and a
   program running, `frozen` is false and `erases_result` is false, so a call
   of either theorem used to reach its native and now runs its case tree,
   counting down the number (not tail-recursive in `equalSound`: `Eq.cong
   Succ (…)`). `set_disabled` is called only from tests
   (`crates/driver/tests/elaboration/erasure.rs`, `indexed_families.rs`,
   `crates/core/tests/it/glue.rs`); no CLI flag or environment variable
   reaches it. I read the 20 examples in `COMPARED_WITHOUT_ERASURE`: none
   has a run-time `decEq`/`sound`/`equalSound` on a big number (the only
   literals of five digits or more are in `mod-arith.sw`'s `byComputing`
   theorems, which are checked, not run), so I expect no failure and at most
   a small rise in the unerased step totals. Neither the lane nor I ran
   them. The verifier should run
   `erasure::erasure_doesnt_change_what_examples_print_or_test`,
   `erasure::proofs_in_data_cost_nothing_at_runtime` and the both-ways tests
   in `indexed_families` for this batch.

2. **Low, docs: `docs/proposals/native-numbers.md` still says both are
   native** (lines 68 and 79 to 81, the "as built: what a native must
   compute" table, including the `eqNatRefl` `k + x` shortcut), and
   `docs/core.md`'s Native implementations paragraph still links to that
   section as its reference. The table needs the two rows and the shortcut
   entry removed, or a line saying they went with rule F (SW-4703).

3. **Note, behaviour change that is intended: a changed library's
   `Nat.equalRefl` / `Nat.equalSound` is no longer refused by pin.** With
   `--std-dir`, a library that alters either proof (or statement) used to be
   refused with `E-BUILTIN`. Now it loads. Nothing trusted depends on them
   any more: omega and derive only build terms that name them, and the
   kernel checks those terms, so a wrong statement gives a failed check, not
   an unsound one. No action; recorded so the trust change is explicit.

## Checked and sound

**(1) Reachability.**

- The machine (`value::unfold_now`): the `frozen` test (theorem, no program
  running) returns the stuck call before `builtins().native(id)` is looked
  up; the only other entries to a native (`from_native`, `run_native`, the
  `Control::NativeArg` continuation) are reached only from there. While a
  program or test runs with erasure, `erases_result` returns the erased
  value before the native lookup. Both theorems are declared `theorem` in
  `std/core/Equality.sw`.
- The reference evaluator (`reference::unfold`): its own copy of the rule F
  test precedes its native lookup. It is used only by tests, never with a
  program running.
- The modes: `program` and `active` are set only by `Erasure::running`
  (`program = true`, `active = !disabled`) and `stop` (both false), so
  "program running, not erasing" exists only under `set_disabled`
  (finding 1). The kernel's own admission checks call `stop`, so they are
  always under rule F.
- Paths that unfold on purpose (`unfolding` lists, `unfold_for`,
  `unfolds_head`, the stuck-call notes at `value.rs` 5470 to 5550): all read
  the body through `body_seen`, which applies `frozen`; the transparency
  set affects `hidden` only, not `frozen`. None of them ever called a
  native, so the removal cannot change them.
- The elaborator's uses (`byComputing`, `byDecision`, `arithmetic`, display
  whnf) go through the same machine. Omega only builds `Nat.equalSound x y
  h` terms.
- The runtimes: `rt::lower` skips a `result_erased` definition before it
  asks `native_op` (both where globals are planned and at call sites), and
  the JS generator's reachability treats `result_erased` as opaque first. So
  the removed `Value::Erased` / `"undefined"` arms were dead. In JS a few
  guards test `is_native` alone (`find_forwarder`, `inline_helper`,
  `unfolds_decision`); the two theorems now take the path every other
  theorem takes there.

**(2) Acceptance, hashes, cost.** Since no checking path reached the
natives, conversion and step counts while checking are unchanged by
construction. The remaining edits are `numbers()` to `arity()` (equal for
every native left) and the registration shape check. Pins hold full hashes
of unchanged declarations; the prelude snapshot still lists the two
theorems' hashes as ordinary entries. Probes, numbers 2^70, all on the
lane's binary (file
`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw4703/review/a.sw`):

| Probe | Result |
|---|---|
| `Nat.equal n n = True` by `byComputing`, and by `Nat.equalRefl n`; the two proofs equal by `byComputing` | checked |
| `J (y p => Nat) 5 (Nat.equalSound n n h)` | checked |
| `match Nat.decEq n n with { holds = True, sound = s, .. } => J … (s byComputing)`, closed and as a function `cmp m n`, with `cmp n n = 7 := byComputing` | checked |
| `n = n` and `n ≠ n + 1` by `Std.byDecision`; two `arithmetic` goals with a `Nat.equal x n = True` hypothesis and conclusion | checked |
| the same casts in `test` blocks (kernel machine, strict, erasing) | 2 passed, ran not cached |
| `stitchwort run` (rt) and `run --reference` printing `cmp n n + five (Nat.equalRefl n)` | 12, 0.35 s each |
| `Char.decEq` cast in a theorem and in a run | checked, prints 7 |

`check --no-cache` of the whole file takes 0.76 s user on the lane's binary
and 0.74 s on main's (with main's std): no countdown anywhere.

**(3) Wire tags.** `nat_tags` is a per-enum position table, so only the two
removed tags (the last two) change. Wire bytes are read only by a runtime
with the same `BUILD_HASH`, which covers core's sources, and a stale
standalone library is refused by `BUILD_MARKER`. The check cache stores no
`Native` value: replay binds natives by name through `bind_builtin_def`,
where `Native::ALL` no longer lists the two, so an old cache entry replays
correctly.

**(4) `docs/core.md`.** The three edited paragraphs are accurate: the
native list, "no theorem has a native" with its reason, the removal of the
pinned-theorem sentences (no pinned declaration is a theorem now; "pins are
on full hashes" stays true), and the `#proof-irrelevance` anchor resolves.
One precision: "a cast along `Nat.equalSound m n h` into data computes by
rule K without counting down `m`" holds when `m` and `n` are convertible,
which is the only case the native covered. `Std core Data.sw`'s doc also
drops `Nat.decEq`, which core.md already said had no native.

**The new test** states what it claims: with 2^70 a countdown could not
finish, so it fails if either rule K or rule F stops applying.

## Not checked

- No test was run (paper review): the natives tests, `hash_stability`,
  `pinned_hashes`, and the erasure-off tests of finding 1.
- Step counts were not compared between main and the branch; equal timings
  and the code reading stand in for them.
- `stitchwort build` (standalone, `--native`, `--js`) was not probed; the
  argument for them is the code reading in (1) and (3).
- The `test-bypass` paths (`register_native_unpinned`,
  `stale_pins_fall_back`).
