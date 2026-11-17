# SW-639 (float laws stage 4): soundness review

Reviewer: Fable paper lane, SW-3804, 17 Nov 2026. Reviewed `lane/SW-639` at `e6c01d77b`
(`git diff main...lane/SW-639`, 5 commits). Paper only: nothing was built or run, so every claim
below is either **[read]** (I read the code that says so) or **[inferred]** (reasoned from what I
read, not observed).

## Verdict: merge after fixes

No soundness finding. The change only removes kernel computation: six operations that had an
always-on `f64` reduction rule now compute by unfolding, and their hardware versions go through
the run-only gate stage 1 built, unchanged. The six model definitions match IEEE 754 and JS on
every case the brief listed. The nine theorems say what their names and docs claim.

Before the merge:

1. **Fix the WebAssembly gate test's count: 3483, not 3489** (F1). As written the test fails
   wherever `web/pkg` is built.
2. **Run `proofs::eta_hold::only_float_add_is_held` by name and update it** (F2). On my reading
   it expects `["Float.add"]` and must now find eight definitions; it may already be failing on
   `main` since stage 3.

The rest (F3 to F7) can be follow-up tickets.

## What I checked, by the brief's items

### 1. `divBits` (`std/Float/Model.sw:200`): correct on every case reasoned [inferred]

| Case | What the code does | IEEE |
|---|---|---|
| either NaN | the NaN | yes |
| ∞ / ∞ | the NaN | yes |
| ∞ / finite (zero included) | infinity, sign xor | yes (`∞ / -0.0 = -∞`) |
| finite / ∞ | zero, sign xor | yes (`1.0 / -∞ = -0.0`) |
| ±0 / ±0 | the NaN | yes |
| nonzero finite / ±0 | infinity, sign xor | yes |
| ±0 / nonzero finite | `roundRatio` sees a zero numerator: zero, sign xor | yes |
| otherwise | `roundRatio (±units a) |units b| 0 xor` | below |

- **Scale.** Both operands are in units of 2^-1074, so the units' ratio is the value;
  `roundRatio` adds 1074 and `roundMagnitude` sees the ratio in units. Correct.
- **Sign.** The numerator is `units a`, negated when `b`'s sign is set, so `Int.isNeg num` is the
  xor for a nonzero quotient, and a nonzero quotient that rounds to zero keeps it
  (`-5e-324 / 3.0 = -0.0`). `-0.0 / -5.0`: `Int.neg (Int.neg (OfNat 0))` is `OfNat 0`
  (`Int.neg (OfNat Zero) = OfNat Zero`, `core/Int.sw:15`), then `zeroBits (xor True True)` is
  `+0.0`. Correct.
- **Exponent with a denominator.** For `n` of `Ln` bits and `den` of `Ld` bits,
  `c = Ld + 53 - Ln` puts `n × 2^c / den` strictly between 2^52 and 2^54; `wide` (one
  comparison, `den × 2^53 ≤ n × 2^c`) picks `c - 1` when it is at least 2^53, so the quotient has
  exactly 53 bits. A negative `c` scales the denominator instead (`scaleDown`). This is the path
  stage 1 built for `den = 1`; with a real denominator the strict lower bound still gives
  `q ≥ 2^52`, so `roundCore`'s precondition holds.
- **Ties to even.** `locate` compares `2r` with the scaled denominator exactly, so a tie is
  found only when the quotient is exactly halfway. `5e-324 / 2.0`: `q = 0`, `Half`, even, `+0.0`.
- **Overflow.** `exponent ≥ 2046`, or a carry out of the largest double, gives bits at or past
  the infinity's, which `roundCore` clamps. `max / 0.5` is `+∞`.
- **Subnormal results.** `exponent = toNat (1074 - c')` is 0 when the quotient is below the
  smallest normal; the shift is then 1074 itself and `q < 2^52` is the fraction.

### 2. `remBits` (`Model.sw:220`): equals JS `%` [inferred]

- NaN for a NaN operand, an infinite dividend or a zero divisor; the dividend itself for an
  infinite divisor (a zero dividend included, sign kept). As ECMAScript's `Number::remainder`.
- Otherwise `r = m - (m / d) × d` on the sizes in units, which is `m mod d`: the truncated
  remainder's size. It is a multiple of the smaller operand's last place and below both `d` and
  (when `m ≥ d`) `m`, so it has at most 53 significant bits at that place and is a double:
  `roundScaled r (-1074)` only packs it (always `Exact`).
- Sign: `Int.signed (signBit a) r`, and `signBit a` as the zero's sign, so `-4.0 % 2.0` and
  `-0.0 % 1.0` are `-0.0`, and `|x| < |y|` gives `x`.
- `Nat.divFuel m m d` with `d ≥ 1` needs at most `m` steps, so the fuel is enough.

### 3. `floorDiv`, `ceil`, `round` (`Model.sw:235-277`): JS's `Math.*` [inferred]

- `floorDiv negative m p`: `q = m / p`; for a negative inexact value `NegSucc q` is `-(q + 1)`,
  the floor; otherwise `Int.signed negative q`, and `Int.signed True 0` is `OfNat 0`.
- `floor`: a zero result comes only from `+0.0`, `-0.0` or `0 < x < 1`, and `zeroSign` is
  `x`'s sign: `+0.0` for the last, `-0.0` only for `-0.0`. `floor (-0.5)` is `-1.0`.
- `ceil = -floorDiv (¬s) m p`: for positive `x`, `-floor (-m/p)`; for negative, `-(m / p)`
  truncated. `ceil (-0.5)` is `-0.0`, `ceil 0.0` is `+0.0` (`floorDiv True 0 p` is exact, so 0),
  `ceil 5e-324` is `1.0`.
- `trunc`: `Int.signed s (m / p)` with `x`'s sign for a zero.
- `round`: `v = units + 2^1073` is `x + ½` exactly, then its floor, then `x`'s sign for a zero.

  | `x` | `v` | floor | result | `Math.round` |
  |---|---|---|---|---|
  | `-0.5` | 0 | 0 | `-0.0` | `-0` |
  | `-0.0` | ½ | 0 | `-0.0` | `-0` |
  | `-0.4` | 0.1 | 0 | `-0.0` | `-0` |
  | `0.49999999999999994` | below 1 | 0 | `+0.0` | `0` |
  | `0.5` | 1 | 1 | `1.0` | `1` |
  | `-2.5` | -2 | -2 | `-2.0` | `-2` |
  | `-0.6` | -0.1 | `NegSucc 0` | `-1.0` | `-1` |
  | `2^52 + 1` | whole + ½ | itself | itself | itself |

  The floor is always a double: below 2^52 it is a whole number under 2^53, and from 2^52 up `x`
  is whole and the floor of `x + ½` is `x`. So `roundScaled` at scale 0 never rounds.
- The Rust native `js_round` (`core/src/float.rs:184`) gives the same on each row, and is exact
  below 2^52 as its comment says [read].

### 4. `isSpecial` (`Model.sw:240`): correct [read]

`Nat.leq 9218868437227405312 (magnitude bits)`: 9218868437227405312 is `0x7FF0000000000000`,
+∞'s pattern. Every valid pattern at or above it without its sign is an infinity or the NaN. The
four roundings return `a` itself there, so `units` never sees exponent field 2047.

### 5. Eta and stuck calls: held by the same rule as `add` and `mul` [read]; goals unobserved

- `eta_held` is `Builtins::has_native(id)` (`value.rs:2532`, `native.rs:222`), which is true for
  any definition in `float_defs` as a `Native`, whatever the switches. The six are registered
  that way by `register_def`, so their record patterns do not open on a neutral argument, in
  `value::branch` (`value.rs:2427`) and in the reference evaluator (`reference.rs:624`).
- So `Float.floor x`, `x / y`, `x / 2.0` and `1.0 / y` on unknown doubles are stuck at the
  definition's head, as they were as primitives, and conversion compares them argument by
  argument. `same_stuck_trees` and `stuck_on_variable` skip them (`float_bound`,
  `value.rs:4512`, `:4533`), as before.
- What differs from a primitive: on a record written out with unknown bits
  (`Float.floor { bits = n, valid = p }`), the pattern matches and the call unfolds to
  `Float.ofBits (Float.Model.floorBits n)`. That is how `Float.Theory.floorOfBits` is proved, and
  the same as `add` since stage 1. A user sees it only after `match x with | { bits, valid }`.
- I found no test or example that shows a goal or failed `byComputing` on `Float.floor x` or
  `x / y`: F4. Stage 3's F4 (`ofInt`/`ofNat` on an unknown number, which no pattern holds) is
  unchanged by this lane.

### 6. The pins: consistent with the snapshot [read]; not recomputed

The six pins in `pins.rs:175-198` are the six hashes in
`library__hash_stability__prelude.snap` (`Std.Float.div` and the rest), which was regenerated in
the last code commit (`1aec6d68c`), after `Model.sw`'s last change (`4f2292e00`, which also
changed `pins.rs`). The diff to `Model.sw` only adds, so the pins of `add`, `mul`, `ofInt` and
`ofNat` are untouched. A stale pin can't bind anything: `register_def` refuses the library with
`E-BUILTIN`, loudly, on the first load. Under D1368 (i) a wrongly blessed pin is a run that
disagrees with checking, not a false theorem; `pins.rs` now says so (stage 3's F8, fixed here).

### The run-only gate: holds for all six on every checking path [read]

- `FloatOp` has one member, `ToText`, and `float::run` returns `None` for it at once
  (`float.rs:710`). Nothing else in `run` computes for a `Primitive`.
- The six reach `f64` code only as `FloatNative`s through `on_pair` and `on_bits`, called only
  from `run`, after `Builtins::float_def(id, running)` (`native.rs:180`) returned a native. That
  function is unchanged: a native only when `running` (or the gate's
  `float_natives_outside_runs`) and natives aren't off. Its two callers are `value.rs:2651` and,
  through `run`, `reference.rs:437`.
- So the kernel's evaluator, the reference evaluator, conversion and `byComputing` (conversion
  in kernel modes, where `in_kernel_modes` clears the running flag) all compute the six by
  unfolding. The WebAssembly kernel is the same crate with no float code of its own. Everything
  in stage 3's review of the gate (`docs/reviews/SW-638-float-stage3-review.md`, item 1) carries
  over; this lane adds enum members and match arms, no new path.
- The check cache [inferred, as in stage 3]: the six's hashes change from primitive hashes to
  content hashes, so an entry made when they had the `f64` rule can't be reused.
- The elaborator admits a bodyless definition as a float primitive only by `FloatOp::named`
  (`elab/src/lib.rs:3578`), which now knows only `Float.toText`.

### The theorems: statements match names and docs [read]

| Theorem (`std/Float/Theory.sw`) | Statement | Verdict |
|---|---|---|
| `Float.divMonotone` (3382) | `0.0 < d → isFinite d = True → x <= y → x / d <= y / d` | True for every `x`, `y` in the total order: finite quotients are rounded monotonically, `-0.0 / d <= 0.0 / d`, a tiny negative rounds to `-0.0`, and the NaN (the greatest) and the infinities are their own quotients. Both hypotheses are needed: `0.0 < d` alone admits `+∞` and the NaN, and the lane's test shows the failure at `+∞`. |
| `Float.ofNatMonotone` (3008) | `m ≤ n → ofNat m <= ofNat n` | True; from `ofIntMonotone`. |
| `Float.ofNatFinite` (3012) | `n ≤ 2^53 → isFinite (ofNat n) = True` | True. The bound is far tighter than the fact (F5). |
| `Float.ofNatPositive` (3964) | `1 ≤ d → 0.0 < ofNat d` | True. |
| `Float.floorLe` (3839), `Float.ceilGe` (3848) | `floor x <= x`, `x <= ceil x`, every `x` | True in the total order: the NaN and infinities are fixed, `floor (-0.0)` is `-0.0`, `ceil (-0.5)` is `-0.0 >= -0.5`. |
| `Float.roundOfWhole` (3920) | `Float.Theory.units x = n × 2^1074 → round x = x` | True, zeros included (`n = 0`, sign kept). For the NaN and infinities it holds if some `n` fits, as the doc says. |
| `Float.roundOfNat` (3935) | `n ≤ 2^53 → round (ofNat n) = ofNat n` | True. |
| `Float.ofNatDivExact` (4010) | `1 ≤ d → d ≤ 2^53 → k × d ≤ 2^53 → ofNat (k × d) / ofNat d = ofNat k` | True, `k = 0` included (`+0.0` both sides). The bounds are what the proof needs (both conversions exact). |

The new std code has no assumption, axiom or attribute that skips checking [read: searched the
diff]. I did not re-derive the proofs.

### Runtimes, JS and the docs

- **JS** [read]. `crates/js` is untouched by the branch: `FloatPrim::Div` is `a / b`, `Rem`
  `a % b`, and `Floor`, `Ceil`, `Trunc`, `Round` are `Math.floor`, `Math.ceil`, `Math.trunc`,
  `Math.round` (`crates/js/src/lib.rs:5709-5714`). The table that feeds it,
  `Representation::float_natives` (`crates/rt/src/natives.rs:782-795`), now takes the six from
  `FloatNative` instead of `FloatOp`, so a definition is in it only if the kernel bound it with
  its pin. The Rust runtime computes the same expressions as before (`rt/src/prims.rs:545-550`).
- **DESIGN.md's row** is true as of this branch: 8 exact operations plus 11 rounding ones are
  the 19 natives; no float rule is left; the trust while checking is the `Nat` natives'.
- **`docs/core.md#float`** is true, with one slip (F3: it lists `Float.sub` among the
  definitions that match on records).
- **`docs/proposals/float-laws.md`** has its "As built (stage 4)" section, and it matches the
  code.

### The WebAssembly kernel

Nothing in the checking path is specific to WebAssembly: the model is `Nat` and `Int`
arithmetic, as for `add` and `mul`, and the natives' `f64` code (`/`, `%`, `floor`, `ceil`,
`trunc`) is what the old primitive rule already ran there. So no soundness question waits on a
WebAssembly run. Two things do need one real run with `web/pkg` built, which Overmind's rolling
check gives: the count (F1), and that the gate's 288 `div` and `rem` pairs and 48 roundings
through the definitions fit the WebAssembly stack guard (`crates/web/src/lib.rs:43`), which is
smaller than the native 2 MiB [inferred: unobserved either way; the work budget is not a
concern at about 24,000 steps a call].

## Findings

### F1. The WebAssembly gate test asserts the wrong count (correctness; tests; fix before merge) [read]

`crates/cli/tests/running/float_paths.rs:518`: `"3489 passed, 0 failed"`.

The WebAssembly gate runs the same two modes as the native test
(`crates/web/src/lib.rs:196`), and the native test's own formula
(`crates/driver/tests/elaboration/float.rs:30`) is
`2 × (1 + 19 + 13 + 72 + 36 + 288 + 720 + 12) + (33 + 72 + 36 + 288 + 720 + 12)`
= `2 × 1161 + 1161` = **3483**. The old figure checks the method: `2 × 819 + 825 = 2463`. The
lane's delta was 1026; the right one is 1020 (6 natives × 2 modes, 336 checks × 2 modes, 336
cross-mode forms). It looks like the 6 new native checks were counted three times.

Scenario: the test passes on any machine without the bundle (it returns early) and fails on
Overmind, or after any `web/pkg` build, with a report that says 3483 passed and 0 failed.

Fix: 3483. Better, print the count from the gate and compare with the same formula, so the two
tests can't drift.

### F2. `only_float_add_is_held` should now find eight definitions (correctness; tests; check before merge) [inferred]

`crates/driver/tests/proofs/eta_hold.rs:79-95` collects every definition with `has_native`
whose body has a `Case` on a type with eta, and asserts the list is `["Float.add"]`. The branch
doesn't touch the file. `Float.div`, `rem`, `floor`, `ceil`, `trunc` and `round` now have both,
by the same shape as `Float.add`, and so has `Float.mul` since stage 3, which is on `main`.

Scenario: the test fails after the merge with a list of eight names. If my reading is right it
is already failing on `main` (SW-638 merged today), and neither the stage 3 lane nor its
verifier selected it. If it passes on `main`, then `Float.mul` isn't held the way
`value.rs:2529` says, and that needs explaining before this merge adds six more.

Fix: run that one test on `main` and on the branch; update the expected list and the test's
name.

### F3. Stale wording left by the move (docs)

None of these is touched by the branch; each describes float primitives that compute.

- `crates/core/src/float.rs:62-64`: `FLOAT_CONTRACT` is "the semantic contract of the float
  primitives: their table, types and reduction rules". It now governs `toText`'s meaning in the
  runtimes only (as the module doc above it says).
- `crates/core/src/reference.rs:33-35`: "Float primitives have no definition to run, so they
  still do." None computes now.
- `crates/core/src/hash.rs:230`: "float primitive `id` (`Float.add`, …)".
- `crates/driver/src/fingerprint.rs:8-9` and `:421`: the toolchain is in the fingerprint because
  "the float primitives are compiled by it". The literal parser is the remaining reason.
- `crates/core/src/pins.rs:117`: "whose `isValid` the float primitives' results rely on" (the
  natives' results).
- `docs/core.md:309`: the list of held definitions that "match on records" includes
  `Float.sub`, which is `Float.add x (Float.neg y)` and has no pattern (`value.rs:2529` has the
  right list). `docs/core.md:357` (row G4) still calls `Float.ofNat` a float primitive (stage
  3's leftover).

Scenario: a reader of `reference.rs` or `fingerprint.rs` concludes the kernel still runs `f64`
code while checking.

### F4. No test shows a stuck `x / y` or `Float.floor x` staying folded (correctness, low; tests) [inferred]

The hold is the same rule that keeps `x + y` (item 5), so I expect goals and messages to show
`x / y` and `Float.floor x`. But the examples that pin this are about sums only
(`examples/reject/float-sum-stays-a-sum.sw`, `float-add-is-held.sw`,
`examples/accept/float-sum-in-a-proof-field.sw`), and `docs/syntax.md:2777` promises it for "a
sum of unknown doubles".

Scenario: a later change to `eta_held` or to how a unary case tree is glued makes a goal about
`Float.floor x` print `Float.ofBits (Float.Model.floorBits x.bits)` and its unfolding, and no
test notices.

Fix (follow-up): a reject example with a failed `byComputing` on `x / y = y / x` and on
`Float.floor x = x`, and the sentence in `docs/syntax.md` widened to every rounding operation.

### F5. `Float.ofNatFinite`'s bound is much tighter than the fact (nit)

`Theory.sw:3012`: `n ≤ 2^53`. `ofNat n` is finite for every `n` below `2^1024 - 2^970`. The
bound is what `ofIntBitsSmall` gives for free, and it is enough for `ofNatDivExact`; the doc
says "up to 2^53", so nothing is misstated. A caller with a 64-bit number can't use it.

Also `Float.roundOfWhole`'s hypothesis is stated with `Float.Theory.units`, an internal name in
a public law (as `Float.ofNatExact` does since stage 3).

### F6. One clause of the `Float.ofNatMonotone` test isn't an instance of the law (nit)

`Theory.sw:3019`: `Float.ofNat 9007199254740993 <= Float.ofNat 9007199254740992` has `m > n`.
It is true because both round to 2^53. Useful as a tie check, but it reads as a mistake; a
comment or the pair the other way round would say what it shows.

### F7. Two items stage 3 passed on are not in stage 4's "Not done" (docs)

The stage 3 record (`docs/proposals/float-laws.md` §10) moved "to stage 4 or a ticket of their
own" the general `toInt`/`ofInt` theorem and `mul`'s monotonicity. Stage 4 did neither, and its
"Not done" list names three other things (`x < floor x + 1`, `rem`'s range, negative whole
numbers for exact `/ 10.0`).

Scenario: with stage 4 the last stage, both drop out of sight unless they have tickets.

Fix: check that each of the five has a ticket, and name the tickets in the proposal.

## Not covered

- Nothing was run: no test, gate, snapshot, pin or timing here is observed. In particular the
  four-paths test's Node leg, which stage 3 broke before its fix, is the lane's result, not
  mine; the orchestrator's verifier should include
  `float_paths::the_four_paths_agree_on_canonical_bits`.
- The proofs' steps (the kernel's job), about 1,070 new lines in `Float/Theory.sw`.
- Whether the pinned hashes are the ones the current tree produces (only that pins and snapshot
  agree with each other).
- `Nat.divFuel`, `Int.subNatNat` and `Int.toNat` were taken to mean what their docs say; I read
  `Int.neg`, `Int.signed`, `Int.isNeg` and `Int.natAbs`.
- The cost of a closed `div` or `floor` in existing proofs and examples (about 24,000 steps
  each, the lane's measurement).
