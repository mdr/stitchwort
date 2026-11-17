# SW-638 (float laws stage 3): soundness review

Reviewer: Fable paper lane, SW-3796, 17 Nov 2026. Reviewed `lane/SW-638` at `7872dea99`
(`git diff main...lane/SW-638`). Paper only: nothing was built or run, so every claim below is
either **[read]** (I read the code that says so) or **[inferred]** (reasoned from what I read, not
observed).

## Verdict: merge after fixes

No soundness finding. The run-only gate is the one stage 1 built, and the three new natives go
through it and nowhere else. `mulBits` follows IEEE 754 in every case the brief listed. The five
theorems say what their names and docs claim.

Before or with the merge:

1. **The Node leg of the four-paths test must pass again** (F1). The orchestrator ran it on
   `main`, where it passes, so this branch broke it. The lane is fixing it; that follow-up commit
   had not landed when this review was written (branch head `a0c1ed9cc`), so it is unreviewed.
   Also re-accept the hash snapshots the lane didn't run.
2. **Write stage 3 into `docs/proposals/float-laws.md`** and file the theorem stage 3 planned but
   didn't prove (F2).
3. **Fix one stale comment** in `crates/core/src/value.rs` (F3).

The rest (F4 to F8) can be follow-up tickets.

## What I checked, by the brief's five items

### 1. The run-only gate: sound [read]

- Every float native is looked up through one function, `Builtins::float_def(id, running)`
  (`crates/core/src/native.rs:180`). It returns a native only when `running` is true (or the
  gate's `float_natives_outside_runs` is set) and natives aren't off. `float_defs` is
  `pub(crate)`; the other two readers, `float_native` and `float_bound`, only report that a
  definition has a native and never compute one.
- `float::run` (`float.rs:724`) is the only code that computes a native's result in the kernel.
  It calls `float_def` with `g.machine.erasure.program_running()`. Its two callers are the two
  evaluators: `value.rs:2650` and `reference.rs:437`. The WebAssembly kernel is the same crate.
- `program_running` is set only by `Erasure::running()`. Outside tests, that is called in
  `driver/src/run.rs`, `test_run.rs`, `driver.rs:1650` and `:1790` (showing a failed test's
  operands) and `elab/src/counterexample/mod.rs` (three places). All of these produce output or
  diagnostics, never a proof.
- Every kernel admission function runs inside `in_kernel_modes` (`machine.rs:73`), which calls
  `erasure.stop()` and so clears the flag whatever the caller was doing. So even if elaboration
  happened inside a run and the unifier used a native's result, the kernel rechecks the term with
  definitions only.
- Cached unfoldings can't carry a native's result across: `Kept::fits` (`value.rs:311`) compares
  the `program` mode. The conversion memo (`TREE_MEMO`) is emptied when the outermost comparison
  ends. `byComputing` is `Term::Refl`, checked by conversion in kernel modes.
- The check cache keeps no evaluated values [inferred: I found no serialisation of `float_defs`;
  `bindings_dump` is the only cache use]. An entry made by an older binary, when `Float.mul` had
  the `f64` rule, is keyed by `Float.mul`'s old primitive hash, which is now a content hash, so it
  can't be reused [inferred].
- `OfInt` and `OfNat` fire only on a known number: `as_nat_with` and `known_int` return `None`
  otherwise, and `known_int` requires the registry's `Int` and its two constructors. `Mul` goes
  through `known_bits`, which requires known, valid bits. [read, `float.rs:741-800`]
- `set_float_natives_outside_runs` has one caller, the gate (`float_gate.rs:339`), after its
  program is loaded. [read]

The lane's change to the gate is three enum members and one early-return arm. It adds no new
path.

### 2. `mulBits` against IEEE 754: correct on every case reasoned [inferred]

`std/Float/Model.sw`, `mulBits` and the stage 1 core it calls.

- **Scale.** `units` gives a finite double as a whole number of 2^-1074: the fraction for a
  subnormal, `(2^52 + f) × 2^(e-1)` for exponent field `e ≥ 1`. A product of two is in units of
  2^-2148, which is the `-2148` passed to `roundScaled`. `roundRatio` adds 1074, so
  `roundMagnitude` sees `n × 2^-1074` in units of 2^-1074. Correct.
- **Exponent.** With `den = 1` and `L = bitLength n`, `c = 54 - L`, `n × 2^c` is in
  `[2^53, 2^54)`, so `wide` is always true and `c - 1` is used: the quotient is in
  `[2^52, 2^53)`. `exponent = toNat (s - (c - 1))` is the exponent field minus 1, or 0 for a
  subnormal (then the shift is `s` itself and `q < 2^52`). `roundCore`'s
  `exponent × 2^52 + rounded` is the right pattern because a normal double's bits are
  `(e - 1) × 2^52 + (2^52 + f)`.
- **Sign.** The units carry the operand's sign, so the product's sign is the xor; a nonzero
  product that rounds to zero takes `Int.isNeg num` (so `5e-324 × -5e-324 = -0.0`: `q = 0`,
  below half, sign set). A zero product takes `zeroSign`, the xor of the sign bits: `(-x) × 0.0`
  and `0.0 × (-y)` are both `-0.0`.
- **Special cases, in order.** A NaN operand gives the NaN. Otherwise an infinite operand with a
  zero operand gives the NaN, and with anything else the infinity of the xor sign (two
  infinities included). Only then is `units` applied, so it never sees exponent field 2047.
- **Overflow.** The largest double is `exponent = 2045`, `q = 2^53 - 1`. At the halfway point
  past it, `q` is odd and the location is `Half`, so it rounds up: the bits become `2047 × 2^52`,
  which the `finite` clamp makes the infinity. Just below halfway stays at the largest. Any
  `exponent ≥ 2046` gives bits at or past the infinity's, clamped the same way.
- **Subnormals.** `exponent = 0`, and `q` is the fraction. Rounding up from `2^52 - 1` gives
  bits `2^52`, the smallest normal double. `5e-324 × 0.5` is `q = 0`, `Half`, even, so `+0.0`;
  `× 1.5` is `q = 1`, `Half`, odd, so 2. Both are in the lane's `Float.Model.mulBits` test.
- **Ties to even.** `locate` returns `Half` only when `2r = d` exactly; `roundsUp` then tests
  the parity of `q`. A carry from `2^53 - 1` to `2^53` lands on the next exponent's bits with a
  zero fraction, which is the right double.
- **Bit length.** A product has up to about 4,196 bits. `bitLengthBy` is exact for any size (it
  falls back to halving) and takes one step per power below 2^8192.

`ofIntBits i = roundScaled i 0 False`: `i × 2^1074` units; zero gives `+0.0`; a negative integer
keeps its sign; nothing nonzero can round to zero. It matches `nat_to_f64` (`float.rs:262`), which
I also read: 53 significand bits, a rounding bit and a sticky bit, exact scaling, infinity above
1,024 bits.

### 3. The pins: can't bind a native to the wrong declaration [read]

- A pin maps a `Builtin` to a content hash. `register_def` (`float.rs:668`) refuses the
  definition unless its hash is the pinned one, then picks the native by
  `FloatNative::builtin() == b` and checks the arity.
- The definition reaches `register_def` by its registry name (`Float.mul`, `Float.ofInt`,
  `Float.ofNat`, `registry.rs:342-350`). Swapping two pins' hashes can't cross-bind anything:
  each declaration's hash is compared with its own builtin's pin, so a swap is refused with
  `E-BUILTIN`.
- A content hash covers the type, the body and everything they refer to, so `Float.mul`'s pin
  covers `mulBits` and the whole rounding core, and `Float.ofNat`'s covers `Float.ofInt`.
- What a regenerated pin can do is bless a changed model without anyone re-reading it. Under
  D1368 (i) that gives a run-time answer different from the checked definition, not a false
  theorem. See F8 for the wording in `pins.rs`.

### 4. The theorems: statements match names and docs [read]

| Theorem | Statement | Verdict |
|---|---|---|
| `Float.mulOneRight` | `x * 1.0 = x` for every `x` | True in IEEE with one NaN: zeros keep their sign, infinities stay, the NaN stays. No hypothesis. |
| `Float.ofNatOfInt` | `Float.ofNat n = Float.ofInt (OfNat n)` | The definition, by `byComputing`. |
| `Float.ofIntMonotone` | `Int.leq i j = True → Float.ofInt i <= Float.ofInt j` | True; `<=` is the total order, and `ofInt` never gives `-0.0` or the NaN, so it agrees with the IEEE order here. |
| `Float.ofNatExact` | `n ≤ 2^53 → units (ofNat n) = OfNat (n × 2^1074)` | True and as documented. See F6 on what it leaves unsaid. |
| `Float.ofNatMul` | `a ≤ 2^53 → b ≤ 2^53 → ofNat a * ofNat b = ofNat (a * b)` | True: both conversions are exact, so the product is rounded once. The bounds are needed for this proof, not too strong. |

The new std code has no assumption, axiom or attribute that skips checking [read: searched the
diff]. I did not re-derive the proofs: the kernel checks those, and the lane reports
`examples::soundness` passing.

### 5. What the lane didn't mention

- **Runtime and JS bindings** [read]. Both take their float operations from one table,
  `Representation::float_natives` (`crates/rt/src/natives.rs:776`), now keyed on
  `FloatNative::Mul`/`OfInt`/`OfNat` instead of the removed `FloatOp` members. A definition is in
  that table only if the kernel bound it, so only with its pin. The JS text is unchanged
  (`a * b`, `Number(n)`, `crates/js/src/lib.rs:5708-5717`), and so is the runtime's arithmetic.
- **The Node leg**: F1.
- **`ofNat n = ofInt (OfNat n)`** [inferred]. In a run, both have natives, so nothing changes.
  The runtimes bind both directly. While checking, `Float.ofNat n` on an unknown `n` now unfolds
  where it used to be stuck: F4. Hashes: everything that mentions the three operations moves,
  as expected for primitive hash to content hash.
- **DESIGN.md's row and `docs/core.md#float`** state the truth as of this branch [read]. The
  proposal doesn't: F2.

## Findings

### F1. The branch breaks the four-paths test's Node leg; two snapshots unrun (correctness; blocks the merge)

- **Node leg.** `float_paths::the_four_paths_agree_on_canonical_bits` fails in its Node leg with
  "nested too deeply for the JavaScript generator". The orchestrator ran it on `main`: it passes
  there in 13 s, so the failure is this branch's [the orchestrator's result, not mine]. My first
  reading was wrong: I expected the same failure on `main`, because the branch doesn't change
  `program()` (`float_paths.rs:128`) or `crates/js`.

  I did not find the cause on paper. What I ruled out [read]: the JS text of the three
  operations is unchanged; they are in `float_natives`, so `is_native` holds for them, and the
  generator's reachability (`set_reach`, `crates/js/src/lib.rs:2399`), forwarders
  (`find_forwarder`), `known_function` and `unfolds_decision` all stop at a native. The error
  comes from `budget.nesting` in `tree`, `tail` or `expr` (`lib.rs:3005`, `:3355`, `:4190`), a
  stack bound on walking one term. So some term the generator walks is deeper on this branch
  than on `main`, or the generator now walks a body it used to skip. The candidates I would
  look at first: a definition that was bodyless and is now reached by a path that doesn't ask
  `is_native`, and a closed expression among the test's values (`1e308 * 10.0`,
  `Float.ofNat (Nat.pow 2 1024)`) that something evaluates before generation, outside a run,
  where it now unfolds the model [inferred, unverified].

  Scenario if merged as is: `main` loses the only test that compares Node with the kernels on
  `ofInt` and `ofNat`, and, depending on the cause, a user's program that multiplies doubles or
  converts a number may fail to compile to JS with `E-RESOURCE`.

  The fix needs its own look when it lands. If it raises a limit or changes which definitions
  the generator treats as native, check that JS still emits `a * b` and `Number(n)` and not the
  model's body.
- **Snapshots.** The lane's ticket note says `hash_stability::float-operations` and
  trip-journal's snapshots "likely move (not run)" [read]. If they do, the verifier fails on the
  merge until they are re-accepted.
- **Not this branch's:** `with_every_native_off_float_runs_out_of_budget` timed out for the
  lane. The orchestrator found it hangs on `main` too and filed SW-3797.

### F2. The proposal has no stage 3 record, and one planned theorem is missing (docs)

`docs/proposals/float-laws.md` §10 plans for stage 3 "the general `toInt`/`ofInt` theorem
(`float.md:1150-1156`)": `Float.toInt x = Some n → x ≠ -0.0 → Float.ofInt n = x`. The branch
doesn't prove it; only the ticket says so. The proposal has "As built" sections for stages 1a
and 1b and none for stage 3, and the branch doesn't touch the file. `docs/proposals/float.md:1154`
still says the theorem waits because `ofInt` has no model.

Scenario: someone reading the proposal believes stage 3 delivered the theorem, or that it is
still blocked.

Fix: an "As built (stage 3)" section (what was built, the five laws, the measured 0.75 ms per
closed `mul`, what was left out), and a ticket for the `toInt`/`ofInt` theorem and for `mul`'s
monotonicity.

### F3. Stale comment on record eta's native rule (docs)

`crates/core/src/value.rs:2529`: "Today only `Float.add` has both a native and a record pattern."
`Float.mul` now has both, and relies on this rule to stay `x * y` on unknown doubles. The branch
doesn't touch the line.

### F4. `Float.ofInt` and `Float.ofNat` on an unknown number now unfold into the model (correctness, low) [inferred]

As primitives they were stuck on an unknown argument. As definitions they have no pattern to
hold them: `Float.ofInt i` evaluates to `Float.ofBitsFrom (roundRatio i 1 0 False) …`, stuck
deep inside `roundRatio` on `Nat.equal (Int.natAbs i) 0`. `eta_held` (the rule that keeps
`x + y` and `x * y` as written) only stops record patterns from opening, and these have none.

Scenario: a goal or failed-conversion message that mentions `Float.ofNat n` for a variable `n`.
The elaborator's gluing should still print the call [inferred], but a comparison of
`Float.ofNat n` with `Float.ofNat m` now walks two unfolded model terms before answering, and
`docs/syntax.md:2777`'s promise ("never `Float.Model` bit arithmetic") is tested for sums only.
Not a soundness matter: conversion decides the same equations or more.

Fix: an example that shows a goal containing `Float.ofNat n` and a failed `byComputing` on one,
to see what prints. If it is the model, hold the conversions as `add` is held.

### F5. The conversions are compared with the hardware on few rounding cases (correctness; tests)

`mul` gets 55 boundary pairs and 150 TestFloat cases through the definition. For `ofInt` and
`ofNat`, the definition meets the hardware on the gate's 7 and 5 numbers
(`float_gate.rs:517-525`), four in `Float.Model.ofIntBits`'s test, and nine in the four-paths
program (`float_paths.rs:110-118`), whose Node leg this branch breaks (F1). They share
`roundScaled` with `add` and `mul`, so the risk is small, and under D1368 (i) a mismatch is a
wrong run-time answer, not a false theorem.

Fix (follow-up): a conversions test like `mul_rounds_like_the_hardware`, with integers of 54 to
1,025 bits built to hit ties, sticky bits and the overflow threshold, both signs.

Related: the `test`s beside the new theorems (`"Float.mulOneRight"`, `"Float.ofNatMul"` and the
others) run with natives on, so they check the hardware against the law, not the model
[inferred from float-laws.md §7.3]. That is useful, but it isn't evidence about `mulBits`.

### F6. `Float.ofNatExact` says less than its doc (nit)

The doc says "so is exactly `n`". The statement gives the units only. That does rule out an
infinity or the NaN (their patterns' units would be 2^2098 and 3 × 2^2097, larger than any
`n × 2^1074` here) [inferred], but for `n = 0` it doesn't say the result is `+0.0`. The internal
`Float.Theory.ofIntBitsSmall` proves all three facts (finite, sign clear, units).

Fix: a public corollary with the sign and finiteness, or `Float.ofNat 0 = 0.0` beside it.

### F7. `Float.ofIntMonotone`'s hypothesis is written as a `Bool` equation (nit)

`(h: Int.leq i j = True)`, where the neighbouring `Float.ofNatExact` writes `n ≤ …`. CLAUDE.md
asks for operators in statements. If `i ≤ j` on `Int` is this same proposition, write it so.

### F8. `pins.rs` calls every pin's staleness unsound (nit)

`crates/core/src/pins.rs:42`: `User::Kernel`, "a stale one is unsound". True for the `Nat`
natives and for `Float` itself (the reducer's records are well typed only for the library's
`isValid`). For the 13 float definitions under D1368 (i), a stale pin would be a run computing
something other than what was checked. This predates the branch (stage 1's `add` and `sub`);
stage 3 adds three more. A second `User` for run-only natives would say it.

## Not covered

- Nothing was run: no test, gate, snapshot or timing here is observed.
- The proofs' steps (the kernel's job) and the proofs of the stage 2 lemmas they use.
- `Int.toNat`, `Int.subNatNat`, `Nat.divFuel` and `Int.signed` were taken to mean what their
  names say (clamping at zero, truncating division).
- The import-cost row for `Float` is new (22,566,104 steps), so there is no earlier figure to
  compare it with.
