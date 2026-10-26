# Proposal: `Float`, a JavaScript number

**Status:** draft 3, signed off after two external reviews; stages 1a and 1b are built ([As
built (stage 1b)](#as-built-stage-1b), [As built (stage 1a)](#as-built-stage-1a)); what §7.2
leaves for later is next, when a program needs it. 23 October 2026. Follows D645 (a JS-number `Float`). Draft 1's
decisions D680 to D689 keep their numbers; draft 2 adopted every point of the first review (D696),
flipping D683 and D685, and added D701 and D702; draft 3 applies every amendment of the second
review (D730) and adds D731 to D733. Every decision is final ([§8](#8-decisions)). Written against
commit `edc645d5`.

Labels: **[checked]** (read in this repository, `file:line`), **[reported by the port
analysis]** (measured or checked by a separate analysis of the motivating app, not re-run here),
**[run]** (run while writing this: Node 22.23.3 and rustc 1.99.0 on macOS/arm64; the snippets are
in [Appendix A](#appendix-a-snippets-run)), **[cited]** (read in the source linked in
[Sources](#sources)), **[cited by the review]** (the reviewer quotes or summarises a specification;
not re-read here), **[inferred]** (my reading, not stated anywhere), **[unverified]** (from
memory, not re-checked).

## As built (`<` and `<=` on `Float` as natives)

A port that moved its time comparisons from `Float.ieeeLe`/`ieeeLt` to `<=`/`<` and `sortOn
.startTime` measured about 6% slower in JS. `Float.compare` already had a native, but `x <= y`
went through `Ord.fromCompare`'s decider: `toBool(Ord.decLessEq(Float.instOrd)(x)(y))`, a
curried call to `Decidable.not(Ordering.decEq(compare(x, y), Greater))`, three objects per
comparison. And against a literal (`t < 10.0`) the search decided the computed proposition,
`Int.less` of two order keys, so JS built `bigint` keys from the bits.

- `Float.instOrd` is a record, as `Int.instOrd` is, with the relations `Float.LessEq x y :=
  Float.leq x y = True` and `Float.LessThan x y := Float.less x y = True`, where `Float.leq` and
  `Float.less` are `Int.leq`/`Int.less` of the order keys, decided by `Float.decLessEq` and
  `Float.decLessThan` (`Bool.decTrue`). Its laws are `Int`'s through the key, as before; the
  four relation laws are `Int.lessOfCompare` and its siblings on the keys.
- `Float.leq` and `Float.less` have natives in the runtimes only, bound by hash like
  `Float.compare` (`crates/rt/src/natives.rs`, `FloatPrim::Leq`/`Less`): in JS, `a < b`, then `a
  > b`, and only on neither (equal numbers, the zeros or a NaN) the NaN and sign cases.
- Where a `Bool` is wanted, `Float.decLessEq x y` is written `Float.leq x y`, as `Int`'s and
  `Nat`'s decisions are (`bind::comparison`); and `Float.LessEq x y` as written is decided by
  `Float.decLessEq` before any search (`bind::float_decider`), so a literal operand changes
  nothing. `x <= y` is `$Std$dFloat$dleq(x, y)`, the same shape as `ieeeLe`.
- `sortOn`, `sort` and `Map Float` are passed `Float.instOrd`, whose `compare` is
  `Float.compare`'s native, as before; what they cost beyond that is the library's curried
  comparator chain (`sortWith` → `sortBy` → `Ord.compare`), the same for every key type.

Node 22, 10,000 random millisecond times, each cell the fastest of 9 processes running one
function (filters 3,000 times, sorts 60 times):

| | before | after |
|---|---|---|
| `filter (t => t <= limit)` | 525 ms | 177 ms |
| `filter (t => Float.ieeeLe t limit)` | 175 ms | 174 ms |
| `filter (t => t < limit)` | 440 ms | 174 ms |
| `filter (t => Float.ieeeLt t limit)` | 176 ms | 175 ms |
| `sortWith (a b => a.startTime <= b.startTime)` | 283 ms | 112 ms |
| `sortWith (a b => Float.ieeeLe a.startTime b.startTime)` | 110 ms | 109 ms |
| `sortOn .startTime` | 177 ms | 176 ms |

The four paths test (`crates/cli/tests/float_paths.rs`) now also checks `<` and `<=` as `Bool`s
and against literals, `Float.less`, `Float.leq`, `Ord.compare`, and six sorts (`sort`, `sortOn`,
`sortWith` by `<=` and `<`, forwards and backwards), the last also against Rust's
`f64::total_cmp`; `examples/extract/float-order.sw` and the `extract` test
`float_order_is_native` check the generated calls.

## As built (stage 1b)

Stage 1b is built as §7.2 defines it: the rest of D687's operations, `Ord Float`, the IEEE
comparisons, the conversions, printing, and the rest of §7.4's table. What it adds:

- **Primitives** (`std/Float/Float.sw`, `crates/core/src/float.rs`), with the 1a trust contract:
  `mul`, `div`, `rem` (`Float -> Float -> Float`; `%` is the truncated remainder, JS's and
  Rust's), `floor`, `ceil`, `trunc`, `round` (`Float -> Float`), `ofInt` (`Int -> Float`) and
  `ofNat` (`Nat -> Float`). Admission now checks each primitive against its own signature
  (`Signature`). `round` is written to the specification's case split (`js_round`), not built
  from `floor(x + 0.5)` or Rust's `round`. The conversions round to nearest, ties to even, with
  infinity from exactly the halfway point past `MAX_VALUE` (`nat_to_f64`: the top 54 bits and a
  sticky bit, not `num-bigint`'s `to_f64`). `toText` (`Float -> Text`) is a primitive with no
  reduction rule, as D688 says.
- **Definitions over the bits, with kernel natives**: `isFinite`, `ieeeLt`, `ieeeLe` (`Bool`s),
  and `toInt` (`Option Int`, every whole double: `Float.toInt 1e100` is the 101-digit integer of
  §2.5, `toInt (-0.0)` is `Some 0`). Their natives return what the definitions compute (`None`,
  `Some (OfNat n)`, `Some (NegSucc n)`, `True`, `False`) and fire only on known valid bits, as
  in 1a.
- **`Ord Float`** (D684): `Float.orderKey` maps the bits to an `Int` (`OfNat bits` with the sign
  clear, `NegSucc magnitude` with it set, so `-0.0` is `-1` and the NaN is greatest),
  `Float.keyOfInjective` proves it injective (four cases, `omega` for one), and
  `Float.instOrd := Ord.fromCompare Float.compare …` takes `equal`, `flip` and `trans` from
  `Int`'s laws through the key. So `<`, `<=`, `List.sort`, `Map Float`, `Set Float` and derived
  orders are the total order, lawful. `<` on `Float` resolves to `Ord` as on any type; nothing in
  `numbers.rs` makes it IEEE.
- **Also**: `Float.ieeeLtLe` (`ieeeLt a b = True -> ieeeLe a b = True`, §4.1), `toSafeInt`,
  `toSafeNat`, `SafeInt.toFloat`, `SafeNat.toFloat`, `Float.toSource` (D733: the four special
  values from the bits, otherwise `toText` with `.0` added when it has no `.` or `e`) and
  `Show Float`. `*`, `/` and `%` on `Float` in `numbers.rs`, with no divisor proof; the D732
  rows for `*` (`-1 * t` is a `Float`, `1.5 * n` a mismatch) are in
  `examples/accept/float-operations.sw` and `examples/reject/float-nat-mul.sw`. The mismatch
  note now names the conversion (`Float.ofNat`, `Float.ofInt`, `Float.toInt`).
- **Runtimes**: every new operation in `crates/rt` (`FloatPrim`) and the JS backend
  (`Math.floor`, `Math.round`, `Number(n)`, `Number.isInteger(x) ? BigInt(x) : undefined`,
  `String(x)`, `<`, `<=`, `Number.isFinite`), with the constructor forms when `Int` or `Text`
  isn't native (the extract test's other two modes). `Float.compare` has a native in both
  runtimes only, bound by hash like `ieeeEq`: in JS, numeric `<`/`>` first, then the NaN, then
  the zeros' signs, so it never reads bits.

**The gate** (`crates/driver/src/float_gate.rs`) now has 1,121 checks per run, on the native
kernel (`crates/driver/tests/float.rs`) and the WebAssembly kernel (`web/pkg`, rebuilt for this
stage; both ran and passed): the program's `rfl` rows for every new primitive (the `Math.round`
cases, `1.0 / -0.0 = -Float.infinity`, `Float.ofNat 9007199254740993 = 9007199254740992`,
`Float.toInt 1e100`, `-0.0 < 0.0`, `toSource` of the NaN); 7 more pairs that must normalise to
the same term; `isNaN`, `isFinite` and `toInt` on 12 patterns and `ieeeLt`/`ieeeLe` on all 144
pairs, each with a neutral witness, giving what they give on the literal; and every normal form
compared across the two modes (natives on; float natives off with the number natives on, as in
1a). All pass.

**The four paths** (`crates/cli/tests/float_paths.rs`): every operation the kernel computes, on
34 values (the edge set plus `-1.5` and `1e100`, and 10 random patterns: every pair for the
binary ones) and 33 literal expressions (the conversions' tie and overflow thresholds, `0.1 *
0.1 - 0.01` for contraction, the `Math.round` cases): 14,279 results, the same canonical bits on
the native kernel, the WebAssembly kernel, the Rust runtime and Node. `toText`, which the
kernels don't compute, has its own test: the Rust runtime's text equals Node's `String(x)` on
5,039 values (the edges, 15 values for each layout of `Number::toString`, 5,000 random
patterns), and every `toSource` reads back through the kernel as the same bits. §7.4 item 6 is
`examples/extract/float-times.sw`, a port of millisecond-time code (`inWindow` with `ieeeLe` and
`ieeeLt`, `latest` with `a > b` as `ieeeLt b a`, `snap` with `Math.round`, `wholeMs`,
`fromCount`, `clamped`), checked against the same functions written in TS on 2,000 random
two-decimal times and edge values: 8,062 comparisons of canonical bits, all equal
(`crates/cli/tests/float.rs`, which also runs generic `==` and `<` helpers, a total-order sort
against the original stable comparator, and printing, under both runtimes).

**Deviations and choices.**

- **`toText` in the Rust runtime isn't `ryu-js`.** No new dependency: Rust's shortest formatting
  (`{:e}`) gives the number of digits, `closest_digits` picks the closest decimal of that length
  with an even last digit on an exact tie, and the layout follows `Number::toString`'s cases
  (`js_to_string`). The tie step is needed: Rust's formatter gives `-1149636667324797.3` for the
  double exactly halfway between that and `…797.2`, which is what Node gives (found by the random
  test; now a unit test). The cross-check is against Node only, as §2.6 promises.
- **`Ord Float` is `Ord.fromCompare` over `Float.compare`, not `Ord.byKey`.** The same key and
  laws, but `<` then decides through one `Float.compare` call, which the runtimes run natively,
  rather than computing two keys from the bits. `Float.compare` has no kernel native: the key is a
  comparison and a subtraction of the bits, which the number natives already compute.
- **`FLOAT_CONTRACT` stays 1.** The new primitives are additions with their own names, so their
  hashes are new anyway; `add` and `sub` mean what they did, and bumping would change every 1a
  hash for no change of meaning.
- **`toInt` uses `Nat.divFuel`, not `/` and `%`.** Elaborating `m / 4503599627370496` needs the
  `auto` proof that 2^52 isn't zero, and that search ran out of depth (`E-RESOURCE`); the exponent
  is passed in from `Nat.divFuel`, which `Nat.div` is defined with.
- **`Float.toSafeNat`** is `Some` only for `Some (OfNat n)` from `toInt`, so `-0.0` gives `Some
  0`, as `toInt` does.
- **`Float.toText` reaches the kernel's `test` evaluator stuck**, as D688 says: a `test` about a
  double's text doesn't run there, and `examples/accept/float-operations.sw` tests `toSource`
  only on the four values decided from the bits. DESIGN.md §3 and docs/core.md now say that
  `toText` is total but not kernel-executable.
- **`web/tests/float-wasm.mjs`** sets `process.exitCode` instead of calling `process.exit`: with
  the report now 1,122 lines, `exit()` cut it off in a pipe, and the test read a partial report.
- **Not built, as §7.2 leaves them for later**: `sqrt`, `min`/`max`, `Float.ofText`,
  `FiniteFloat`, an operations record in std, and the general `toInt`/`ofInt` theorem. Of §6.1's
  facts, `neg (neg x) = x` (1a) and `ieeeLt a b = True -> ieeeLe a b = True` are proved; the
  others (`ieeeEq` symmetric, `toInt` facts) aren't, since nothing needs them yet.

## As built (stage 1a)

Stage 1a is built as §7.2 defines it, in its five steps, each step's tests passing before the
next. What it adds, by step:

1. **The gate.** `std/Float/Float.sw` declares the type, `isValid`, `Bool.canonicalTrue`,
   `Float.make`, `nan`, `infinity`, `isNaN`, `neg`, `abs`, `bitsExt` (with `mkExt`), `bitsNe`,
   `decEq` (through `decEqFrom`) and its `DecEq` instance, `isZero`, `ieeeEq`, the primitives
   `add` and `sub`, and the proof `Float.negNeg : neg (neg x) = x`, with its lemmas about the
   sign bit. `crates/core/src/float.rs` admits the primitives, reduces them on known bits (always
   on), and has natives for `neg`, `abs`, `isNaN` and `decEq`. `FLOAT_CONTRACT = 1` is hashed
   into each primitive's hash (`hash::float_primitive_hash`). The elaborator has decimal literals,
   `Kind::Float` and D732's order. The gate is `crates/driver/src/float_gate.rs`, run by
   `crates/driver/tests/float.rs` on the native kernel and, through the playground's
   `float_gate` export and `web/tests/float-wasm.mjs`, on the WebAssembly kernel.
2. **The front end.** `Tok::Float`, the rule that a number right after `.` is digits only, the
   literal refusals (`E-FLOAT-LITERAL`), and §2.4's table as `examples/accept/float-literals.sw`
   and `examples/reject/float-*.sw`. The pretty-printer shows a double with known bits as its
   literal, so `rfl` failures read `` `Float.add 0.1 0.2` and `0.3` aren't equal``.
3. **Run time.** `Value::Float(f64)` in `crates/rt`, made only by `Value::float`, which makes a
   NaN canonical. Generated JS has the canonical-bits module (`FLOAT_BITS` in `crates/js`). In
   both, the record's constructor with run-time bits goes through the bits (`FloatPrim::FromBits`,
   `fromCanonicalBits`), and matching the record, which is what `.bits` is, gives them back
   (`FloatPrim::Bits`, `toCanonicalBits`).
4. **The boundary.** `Boundary::Float`, the `FLOAT` codec (every `number`), `number` in the
   `.d.ts`, and `Float` among the built-in boundary forms (D613): `js.*` attributes on it are
   refused. `examples/extract/floats.sw`.
5. **Plumbing.** `crates/driver/build.rs` hashes `rustc -vV` and `TARGET` into `FINGERPRINT`,
   through `crates/driver/src/fingerprint.rs`. `crates/cli/tests/float_paths.rs` compares the
   native kernel, the WebAssembly kernel, the Rust runtime and Node on every 1a operation over 32
   values (the §7.4 edge set and 10 random valid patterns, every pair for the binary operations)
   and 10 literal expressions, 4,234 results, as canonical bits shown in hex. The contract
   plumbing rows are tests in `crates/driver/tests/float.rs`.

**The gate's mode (agreed with the coordinator).** The gate runs with natives on, and with the
float natives off and the number natives on (`Builtins::disable_float_natives`, new). It doesn't
run in the `n0` mode §3.4 names, every native off, because there no `Float` can be evaluated at
all. Every bit pattern is a 64-bit number, and `Float.isValid` compares it with
`Nat.leq n 9218868437227405312`; without the number natives `Nat.leq` counts down one `Succ` at a
time, about 9·10^18 steps. Evidence: with every native off, loading a program that imports
`Float` fails with `E-RESOURCE` ("it took more evaluation steps than allowed") at a work budget
of 2·10^6 steps, and still at 2·10^9 steps (104 s); a test keeps the first
(`with_every_native_off_float_runs_out_of_budget`). The review's concern, that the float natives
agree with their definitions, proof fields included, is exactly what the float-natives-off mode
checks: the definitions then compute on their bits with the number natives, which are trusted and
tested separately (`crates/driver/tests/natives.rs`). In that mode every row passes: the six
`rfl` rows; `neg` and `abs` of `{ bits = k, valid = p }` with `p` a variable, on 12 bit patterns,
normalise to `{ bits = k', valid = rfl }`; `neg (neg 1.5)` normalises to the literal and
`neg nan` to `Float.nan`; `decEq` gives `Yes (Float.bitsExt x y rfl)` and
`No (Float.bitsNe x y (Nat.equalFalse m n rfl))`; and every normal form, compared as a term, is
the same in both modes. 107 checks, on both kernels.

**Deviations and choices.**

- **`isValid`** is written as the three valid regions (`n <= +∞`, the NaN, `2^63 <= n <= -∞`)
  rather than "below 2^64 and, if a NaN pattern, the canonical one"; the two agree on every `n`.
  `neg` is defined through `Float.negFrom x (Float.isNaN x) rfl` rather than an `if`, so that the
  proofs can take the NaN case apart; the sign flip's validity is `Float.flipValid`, proved with
  `omega`.
- **Natives are bound by content hash in the kernel**, not by name and type alone as the number
  natives are: `Float` (`FLOAT_DATA_HASH`, which covers `isValid`) and each definition with a
  native or referred to by one (`NATIVE_HASHES`). A library that doesn't match is refused with
  `E-BUILTIN`, rather than silently losing its natives, since the primitives can't work without
  `Float` and `decEq`'s native names `bitsExt` and `bitsNe`. The runtimes use the kernel's
  binding, plus `Float.ieeeEq`, bound by hash in `crates/rt/src/natives.rs` (it has no kernel
  native).
- **`std/Float/Float.sw` isn't cached** by the check cache: it declares primitives and binds
  natives, which replay can't do. It checks in a fraction of a second. The check-cache test now
  expects exactly this file to be uncacheable.
- **D58** (no decision procedure in a library file): `Float.decEq` and `Float.decEqFrom` are one,
  because the native needs a definition of its own. They decide only equations between `Float`s,
  which can't be written without loading the file, so `auto` still can't depend on what else is
  loaded; the D58 test lists them as the exception.
- **D732, with a minus sign.** Pass 1 decides only on an `Int` or a `Float` operand when the
  group has a prefix `-`; any other operand is left inferred, the `-` makes the group `Int`, and
  that operand's mismatch is reported as before. So no existing error message changed (§2.4
  expected some to). Every existing example and snapshot is unchanged.
- **`*`, `/` and `%` on `Float`** are refused in 1a (`` `*` isn't defined on `Float` yet``), and
  `<` and `<=` go through `Ord`, which has no `Float` instance until 1b. So §2.4's rows `-1 * t`
  and `1.5 * n` are tested as `+`, and `-(Float.ofInt 5)` as `-(Float.abs 1.5)`.
- **Literal errors** have their own code, `E-FLOAT-LITERAL`. `Float.infinity` is in 1a because
  the overflow message names it.
- **The WebAssembly kernel's paths** (the gate and the four-path test) run from `web/pkg`, the
  playground's bundle. The tests leave that path out, saying so, when it isn't built or was
  built from other sources (its `source_fingerprint`, the build fingerprint without the toolchain
  and target, differs from the tests' `SOURCE_FINGERPRINT`). For this
  stage it was built and both ran.
- **The fast JS codec** (merged from main) uses the `FLOAT` leaf directly, so a `Float` takes
  the fast path, `-0`, `NaN` and the infinities included.
- **The extract test's comparisons** now encode `-0`, `NaN` and the infinities as text, so a
  `Float` result compares as the same double rather than through JSON.
- **The run-time audit** of typed arrays allows the `stitchwort run --js` runner's
  `Int32Array` over a `SharedArrayBuffer`, which only sleeps and reinterprets no bits.
- **The build fingerprint's framing** changed with the refactor into `fingerprint.rs`, so every
  build's fingerprint is new once (both caches start fresh).

## Response to review (round 2)

The second review approved the architecture and both flipped decisions (D683, D685) and asked only
for tighter specification, plus one early implementation check: that ordinary kernel natives keep
the definitional behaviour, proof fields included, of the definitions they replace. Every amendment
is applied (D730). One disagreement, on a point the review left open: `toSource` turns out to be a
language-level function (a field of `Show`), so it is specified rather than treated as compiler
tooling (D733).

| Review point | Change in draft 3 |
|---|---|
| §2 Bit extensionality is a propositional theorem; it doesn't give definitional agreement | §3.4 now separates the two. `Float.bitsExt : x.bits = y.bits -> x = y`, proved with `Bool.uniqueEq` as `SafeNat.ext` is, is what `DecEq Float`, the total-order key's injectivity and `neg (neg x) = x` use |
| §2 Ordinary natives must agree with their definitions on proof fields; negative literals cross the `Float.neg` path | §3.4: the requirement is stated (it is already the native-number rule, [checked] `crates/core/src/native.rs:13-17`). Chosen approach (D731): every exact definition returning a `Float` builds it with one checked constructor, `Float.make`, whose witness reduces to `Eq.refl True` on known bits whatever proof it is given; natives fire only on known bits and return the same record |
| §2 Acceptance checks, natives on and off, compared by conversion | §3.4 table; it is **the first gate of stage 1a** (§7.2) |
| §3 Typed operands must outrank the unary-minus default | §2.4: concrete constraints (expected type, decimal/exponent literals, typed operands) are collected first; `-` only defaults an otherwise undecided group to `Int`. What changes in `numbers.rs` is stated (D732). The review's seven cases are in §2.4's table and §7.4 |
| §4 `toInt`/`ofInt` round trip fails on `-0.0`; the general inverse theorem has no model to prove it from | §6.1: the stated relation excludes `-0.0`; stage 1 promises proofs about the exact decoder and concrete computations only; the general theorem is deferred until `ofInt` has a model. §7.2 drops it from the bit-lemma uncertainties |
| §5 D701: one audited module, both directions | §3.5, D701: `toCanonicalBits` and `fromCanonicalBits`, with their two laws; `.bits`, the dynamic constructor, ordering and hashing go through them; all typed-array/`DataView` code lives there |
| §5 "NaN is decoded to the canonical NaN" | §5: a statement about the logical value under α, not the JS number's payload |
| §5 Differential tests compare canonicalised bits, the TS oracle's too | §6.4 item 4, §7.4 |
| §6 `toText` doesn't have the shared semantics; extend α to every type; the kernel limitation covers any consumer of the string; runtime totality vs kernel executability; `toSource` | §3.3 (scope of the equation, α per type), §2.6 (backend-supplied interpretation, consumers, totality), D733 (`toSource`) |
| §7 Literal underflow condition; two sentences | §2.3: the condition is "mathematically nonzero, rounds to zero"; the table and both sentences fixed |
| §7 D702: an erased proof checks nothing | §5, D702 |
| §8 `>`/`>=` translation keeps operand evaluation order | §4.1, §6.4 item 5 |

## Response to review (round 1, draft 2)

(Kept as written for draft 2. Where round 2 changed a point, the round-2 table above and the body
take precedence: notably D701's "one representation-sensitive operation" is now one audited
module with two directions.)

The review approved the architecture (canonical bits, selected primitives, staged scope, a local
lawless `TimeOps`) and asked for corrections and two policy changes. Every point is adopted; I
disagree with none. Where the review offered a choice, the choice made is stated.

| Review point | Change in draft 2 |
|---|---|
| §1 Consistency vs IEEE agreement vs backend preservation are three different claims; state the commuting equation α(runtimeOp(x, y)) = modelOp(α x, α y) | New §3.3, the trust contract, with the equation governing arithmetic, constructors, projections, equality, ordering and constant folding |
| §1 "No axioms" needs qualifying | §3.2 now says "no new propositional axioms, but new trusted reduction rules"; replacing them with checked definitions later is a real assurance gain |
| §1 Reducer returns a properly typed record with its validity witness | §3.4: the reducer returns `{ bits = k, valid = Eq.refl True }`, the same term the literal elaborator builds; no unchecked-proof mechanism |
| §1 Execution conditions (rounding mode, subnormals, signed zero, NaN, no reassociation/FMA, FP environment) | §3.3, conditions C1–C6 |
| §1 Reduce on normalised values, not literal syntax | §3.4: the rule fires on forced arguments whose `bits` force to a number |
| §1 Primitive identity: `add`/`sub`/`mul` share a type | §3.3: each primitive's hash carries its name as an operation tag, as `Delay`'s constants already do ([checked] `crates/core/src/hash.rs:96-104`), plus a contract version |
| §1 Versioned semantic contract; implementation fingerprint in the cache | §3.3 "Caches": the build fingerprint already covers the kernel's source and `Cargo.lock`, but not the Rust toolchain; that is added, plus `FLOAT_CONTRACT` in the primitives' hashes |
| §1 "A future full model changes no program" | §6.3: source behaviour stays compatible; hashes change and everything downstream is rechecked |
| §2 `neg` as a sign flip breaks the invariant on NaN | §2.2: `neg` has an explicit NaN case; `neg (neg x) = x` still holds. Rust's `-NaN` is `0xFFF8…` [run] |
| §2 Canonicalising only `.bits` needs every representation-sensitive operation audited; choose an invariant | §3.5, new D701: physically canonical in the kernel and the Rust runtime (one constructor); in JS the only representation-sensitive operation is `.bits`, which canonicalises. Audit list, including `f64::total_cmp` ordering negative NaNs first [run] |
| §2 Boundary guarantee covers the value abstraction, not NaN payloads | §5 |
| §3 Keep `==`/`!=` lawful; IEEE equality explicitly named; same for `<` | **D683 flipped.** §4: `== != < <=` keep their existing meanings (`DecEq`, `Ord`); ported `===`, `<`, `<=` become `Float.ieeeEq`, `Float.ieeeLt`, `Float.ieeeLe`. The review's refactoring examples are in §4.2 |
| §3 Elaboration, inlining, specialisation and backends keep the operation distinct | §4.4 |
| §4 Theorem-holds vs same-behaviour-as-TS are separate arguments | New §6.4, port verification obligations |
| §4 Total order changes a stable sort's output on `+0`/`-0` ties | §4.5, §6.4; checked [run] |
| §4 JS `Map`/`Set` use SameValueZero | §4.5 |
| §5 Plain `Float` accepts every JS number | **D685 flipped.** §5; finiteness belongs on a refinement or the application's types (new D702) |
| §5 JSON claim wrong (`JSON.parse("1e400")` is `Infinity`; finite inputs don't give finite intermediates) | §5, corrected [run] |
| §6 `Number::toString` allows several shortest outputs | §3.6, D688: `toText` doesn't reduce in the kernel in stage 1 |
| §6 RoundMVResult is implementation-defined after 20 digits | §2.3: the literal is elaborated to bits once; JS is generated from the bits |
| §7 Full `Math.round` rule; the large-integer case | §2.5, with the four cases [run] |
| §7 `toInt` over the full range, as a definition | §2.5: `Float.toInt` is an ordinary definition over the bits with a native, not a primitive |
| §7 "partial" in a "Total?" column; `toInt (-0.0)` loses the sign | §2.5 |
| §7 Defaulting examples (`-1 + 0.5`, `0.5 + -1`, `-0`), overflow, underflow, large whole literals | §2.3–2.4, with a table of examples |
| §7 Chained numeric projections (`xs.0.1`) | §2.3: they don't exist today ([checked] `crates/syntax/src/parser.rs:2661-2673`); a lexer rule and regression test keep it so |
| §7 `sqrt` is "correctly rounded", not "exact"; later `min`/`max` must specify JS's NaN/`-0` rules | §3.6 |
| §8 `TimeLaws` comment must name the operations | §6.2: `TimeLaws Float Float ieeeTimeOps` |
| §8 "Not provable" too absolute | §6.1: "no practical general reasoning framework for rounded arithmetic in stage 1" |
| §8 Test the four execution paths; the table | §7.4 adopts the table |
| §8 Line counts are code-size guesses; start with a thin end-to-end slice | §7.2: stage 1a is the reviewer's slice; the main uncertainty is named |

Two places where I went slightly beyond the review, both in its direction:

- **Literal overflow and underflow are refused** (`1e400`, `1e-400`), where the review only asked
  for a decision (§2.3).
- **The Rust toolchain goes into the build fingerprint** (§3.3). The review asked for an
  implementation fingerprint "if this is not already present"; it mostly is, but the compiler's own
  `str::parse::<f64>` isn't covered by it, and literals depend on it.

## 0. Summary

A real-world TypeScript app is being ported so that its exported Stitchwort code can be called
directly from TS. Its data has millisecond times that are sometimes fractional (`80281.87`, from
unrounded audio clock arithmetic), and the code adds, subtracts and compares them. Today a number at
the JS boundary is a `bigint` (`Nat`, `Int`) or a whole `number` (`SafeNat`, `SafeInt`, fractions
refused, [checked] `crates/js/src/lib.rs:2574-2597`), so these values can't cross.

The proposal:

- **`Float`** in `std/Float`, a 64-bit IEEE double. At run time it is the real JS `number` (and a
  Rust `f64` in the runtime). It crosses the boundary as `number`, any `number` (D685).
- **In the logic** it is a record of the double's 64 bits, `{ bits: Nat, valid: … }`, with exactly
  one NaN. This is the shape Lean 4 uses [cited]. Equality, the total order, negation, absolute
  value, the IEEE comparisons and `toInt` are ordinary Stitchwort definitions over the bits, so they
  can be reasoned about. They build results through one checked constructor, so that their kernel
  natives agree with them definitionally, proofs included (§3.4, D731). The rounding operations
  (`+ - * / %`, `floor`, `round`, `ofInt`) are **bodyless primitives**: the checker computes them with Rust `f64` when their arguments are known
  doubles, under an explicit trust contract (§3.3), and otherwise treats them as unknown functions.
- **Operators keep their meaning (D683):** `==`, `!=`, `<`, `<=` on `Float` are the same lawful
  operators as on every other type: `==` is `DecEq` ("the same double", like `Object.is`), `<` is
  `Ord` (IEEE `totalOrder`). JS's `===`, `<` and `<=` are written `Float.ieeeEq`, `Float.ieeeLt`
  and `Float.ieeeLe` in ported code. `+ - * / %` are the IEEE operations, in the order written.
- **Proofs:** stage 1 proves structural facts (a filter keeps only times after `start`; a sort's
  output is sorted by `Float`'s total order) and facts about known doubles by computation (`0.1 +
  0.2 = 0.30000000000000004` by `rfl`). Facts needing algebra (`(t - s) + s = t`) are false for
  doubles and are proved for exact types, through code written over a small operations record.
  That a proved port *behaves like the TS* is a separate obligation (§6.4).
- **Later, not now:** giving the rounding operations real definitions over the bits (Lean's model,
  or Flocq's), which would turn the primitives into ordinary natives bound by hash.

## 1. How other languages do it

| Language | Float type | In the logic | Equality |
|---|---|---|---|
| **Lean 4** | `Float`, a structure over `Float.Model`, "a subtype of `UInt64`" where "bit patterns encoding a `NaN` must be exactly a chosen canonical `NaN`" [cited] | `add`, `sub`, `mul`, `div`, `sqrt` and the integer conversions "have a logical model in terms of `Float.Model`" and are compiled to C operators; `pow`, `exp`, `round`, `floor`, `toString`, trig "do not reduce in the kernel" [cited]. The reference says the model is not meant for lemmas: "not a goal … to have any direct lemmas written about it at all" [cited]. Its runtime agreement guarantee is qualified by FFI code not changing the floating-point environment [cited by the review] | `==` is IEEE, "not a reflexive relation" [cited]. Lean's `==` is `BEq`, which doesn't promise reflexivity or agreement with `=`; `LawfulBEq` adds that separately [cited by the review]. Stitchwort's `==` is `DecEq`, so lawful by construction ([checked] `crates/elab/src/std/core/DecEq.sw:11-12`) |
| **Rocq** | primitive `float` (binary64) | Operations are axioms relating each primitive to a Flocq-style spec through `Prim2SF` (e.g. `mul_spec`); they are "regular axioms … listed by `Print Assumptions`". `vm_compute`/`native_compute` use the processor's IEEE operations [cited] | `eqb` is IEEE (`eqb nan nan = false`, `eqb +0 -0 = true`); a separate `Leibniz.eqb` is identity [cited] |
| **Isabelle** | AFP `IEEE_Floating_Point`: a full formal model, `('e,'f) float`, with a single-NaN variant and code generation [cited] | the model itself; used by CakeML [cited] | model's IEEE `≐` vs HOL `=` [unverified] |
| **F\*** | `FStar.Float64`: `val t : Type0`, abstract, no exposed model [cited] | `add`, `sub`, `mul`, `div`, `lt`, `lte`, `of_int`, `of_literal` | `ieee_eq` (NaN false, ±0 equal) and `bit_eq` (NaN equals itself, ±0 differ); `t` is not an `eqtype` [cited] |
| **Dafny** | none found: release notes mention no float type [cited]; `real` is an exact mathematical real, compiled to a rational [unverified] | exact reals | exact |
| **Liquid Haskell** | `Double` is encoded to the SMT solver's reals, so proofs treat it as exact [cited: secondary source] | reals (so a proof may not hold of the doubles actually computed) [inferred] | — |
| **Agda** | primitive `Float`, binary64 "with exactly one NaN value" in the type checker [cited] | primitives compute in the checker | `primFloatEquality` is IEEE ("not reflexive"); a lawful equality is built from `primFloatToWord64 : Float → Maybe Word64` and its injectivity lemma, which "cannot be guaranteed to be consistent across backends" [cited] |
| **Idris 2** | primitive `Double` | primitives compute | no lawful `DecEq Double` in `Decidable.Equality`; primitives' `DecEq` comes from `Eq` via `believe_me`, described as "unsafe" [cited] |
| **ReScript** | `float` = JS number; `int` is narrower (data "might get lost" with large numbers); float has its own operators `+.`, `-.` [cited] | — | JS |
| **PureScript** | `Number`: "A double precision floating point number (IEEE 754)"; `Int` is 32-bit [cited] | — | JS |
| **Elm** | `Float` (IEEE 754, "e.g. `NaN`"), `Int` safe to ±(2^53 − 1) on JS [cited] | — | JS |

What to take from this:

1. **Bits with one NaN is the common model** (Lean, Agda, Isabelle's single-NaN variant). It makes
   "the same double" a decidable, lawful equality.
2. **Every system that keeps a lawful equality also offers IEEE equality separately** (Rocq's two
   `eqb`s, F\*'s `ieee_eq`/`bit_eq`, Agda's primitive vs. word equality, Lean's `==` vs `=`). The
   ones that make the operator IEEE (Lean) do so because their operator class was lawless to begin
   with; Stitchwort's isn't, which is why D683 now keeps `==` lawful (§4).
3. **Nobody proves algebraic laws about doubles in everyday code.** The full models (Flocq,
   Isabelle) exist for numerical-analysis proofs, and Lean says outright its model isn't for lemmas.
4. The JS-targeting languages all take JS numbers as they are, NaN and all.

## 2. The type and its syntax

### 2.1 Name and place

`Float` (D680, decided), in `std/Float/Float.sw`, loaded on import like `SafeInt` ([checked]
`crates/elab/src/std/Int/Safe.sw:14-16`). `Float` is what Lean, Agda, Elm and ReScript call it
[cited], and what a TS programmer expects.

### 2.2 The definition and the representation invariant

```
-- A 64-bit IEEE 754 double: its bits, with every NaN as the one NaN (0x7FF8000000000000).
type Float = { bits: Nat, valid: Float.isValid bits = True }
```

**The invariant.** `Float.isValid n` is `n < 2^64` and, if `n` is a NaN pattern (exponent all
ones, fraction non-zero), `n = 0x7FF8000000000000`. Every `Float` value satisfies it, in the logic
by the `valid` field and at run time by D701 (§3.5). Two doubles are equal as values (`x = y`)
exactly when their bits are, so `0.0` and `-0.0` are different values and there is one NaN, equal
to itself. This is `Object.is` [inferred; `Object.is(-0, 0)` is false [run]].

Draft 1 described `neg` as "flip the sign bit". That isn't closed under the invariant: flipping the
canonical NaN gives `0xFFF8000000000000`, which `isValid` refuses, and Rust's `-f64::NAN` gives
exactly that pattern [run]. So:

```
-- The one way exact definitions build a `Float` (D731, §3.4). The witness is computed from the
-- bits: on known bits it is `Eq.refl True`, whatever `p` is.
def Bool.canonicalTrue: (b: Bool) -> b = True -> b = True
  | True, _ => rfl
  | False, p => p          -- unreachable in practice; any closed proof would do
def Float.make (n: Nat) (p: Float.isValid n = True): Float :=
  { bits = n, valid = Bool.canonicalTrue (Float.isValid n) p }

def Float.neg (x: Float): Float :=
  if Float.isNaN x then Float.nan
  else Float.make (Float.flipSignBits x.bits) (Float.flipSignValid x …)  -- bits ± 2^63
```

(`flipSignBits` and `flipSignValid` are illustrative: the first adds or subtracts 2^63, the second
proves the result valid from `isNaN x = False`.) `neg (neg x) = x` still holds: for NaN both sides
are `Float.nan`, otherwise the flip is an involution that keeps `isNaN` false; the two records have
equal bits but possibly different `valid` proofs, so the proof ends with `Float.bitsExt` (§3.4)
[inferred; to be proved in stage 1a]. `abs` (clear the sign bit) is closed already, since the
canonical NaN's sign bit is clear [inferred]; it too returns `Float.make …`, never its argument
unchanged (§3.4 explains why).

The lesson the review draws, which this draft follows: "exact on the bits" doesn't by itself mean
"keeps the invariant"; each definition over the bits gets its `valid` obligation discharged in
Stitchwort, so the kernel checks it.

### 2.3 Literals (D686)

**Forms:** `1.5`, `80281.87`, `0.25`, and with an exponent `1e3`, `1.5e-7`, `2.0E21`. A digit is
required on both sides of `.`, so `5.` and `.5` stay errors. An exponent is `e`/`E`, an optional
sign, and at least one digit.

**Meaning:** the decimal value correctly rounded to binary64, ties to even. That is Stitchwort's
definition, not "what JS gives": ECMAScript's RoundMVResult lets an implementation treat digits
after the twentieth significant one as it likes, and numeric literals and `Number(text)` use it
[cited by the review]. Writing a decimal point or an exponent is the request for rounding: `0.1`
is the double nearest 0.1, as everyone expects.

**One elaboration, then bits.** The literal is converted to canonical bits once, by the elaborator.
The term is the record with those bits (a `Nat` literal) and the standard witness (§3.4). So:

- the hash is of the bits, and `0.10`, `0.1` and `1e-1` hash the same [inferred: the hash walks
  the term, [checked] `crates/core/src/hash.rs:1-6`];
- the spelling is kept in the AST for diagnostics and spans only;
- generated JS writes the number from the bits, as the shortest round-trip spelling (the `ryu-js`
  output, §3.6) or `-0`, never by re-emitting the source spelling. The runtime builds it with
  `f64::from_bits`.

Rust's `str::parse::<f64>` is the conversion. It agrees with Node on `80281.87`
(bits `4680253341308362424` in both) [run]. Rust's parser has been correctly rounded since 1.55
[unverified]; §7.4's differential test checks it on many strings, which shows agreement with the
tested engine, not the language's definition.

**Edge cases, decided:**

| Source | In a `Float` group | Reason |
|---|---|---|
| `0.1`, `80281.87` | the nearest double | decimal syntax asks for rounding |
| `9007199254740994` (2^53 + 2) | accepted, exact | it is a double [run] |
| `9007199254740993` (2^53 + 1) | **refused**: "not exactly a `Float`; the nearest are `9007199254740992` and `9007199254740994`" | JS silently gives `9007199254740992` [run]; a whole literal reads as exact, so rounding it is a surprise. Write `9007199254740992` or `9007199254740993.0` to ask for rounding |
| `1e400`, `-1e400` | **refused**: "too large for a `Float`; use `Float.infinity`" | JS and Rust give `Infinity` [run]. Turning a literal into infinity is a much larger change than rounding, and a program that means infinity can say so |
| `1e-400`, `-1e-400` | **refused**: "too small for a `Float`: it would be `0.0`" (or `-0.0`) | JS and Rust give `0`, and `-1e-400` gives `-0` [run]. Rounding a tiny nonzero value to zero is a valid IEEE result; the language chooses to diagnose it in literal syntax, where it is almost certainly a mistake |
| `0.0`, `-0.0`, `0e-400`, `0e400` | accepted: `0.0` (`-0.0` for the second) | the mathematical value is zero, so nothing was lost |
| `5e-324` | accepted: the smallest subnormal | nonzero, and its rounded value is nonzero |

**The underflow rule, precisely:** a literal is refused when its mathematical decimal value is
nonzero but its correctly rounded binary64 value is zero. (The overflow rule: refused when the
correctly rounded value is infinite.) Both look at the unsigned literal; a leading `-` is
`Float.neg` (§2.4), so `-1e-400` is refused for the same reason as `1e-400`. Arithmetic and the
explicit conversions keep IEEE overflow and underflow; only literal syntax is restricted.

The alternative for overflow and underflow is to accept the literals as JS does. They are refused
because the motivating port doesn't need either and both read as mistakes; accepting them later is
a one-line change.

**Lexing:** a new token `Tok::Float` holding the source text. Today a number is digits only
([checked] `crates/syntax/src/lexer.rs:248-255`). `.` after digits joins the number only when a
digit follows, so `1..n` and `[x, ..rest]` are untouched, and qualified names need a letter after
`.` ([checked] `lexer.rs:194-198`).

**Numeric projections.** Stitchwort has no `xs.0` or `xs.0.1`: after `.`, the parser accepts only
a name, otherwise "expected a field name after `.`" ([checked] `crates/syntax/src/parser.rs:2661-2673`);
pairs use `.fst`/`.snd` ([checked] `docs/syntax.md:984`). So `0.1` as a `Float` token can't break
existing code. To keep the door open (Rust had exactly this problem with `t.0.1`), the rule is:
**a number that starts immediately after a `.` (no space) is digits only, never a `Float`**. A
regression test lexes `xs.0.1` as `xs` `.` `0` `.` `1` (and the parser then gives today's error),
`p.fst.snd` unchanged, and `1.5` and `x.y` as before.

### 2.4 Groups and defaulting

**Today.** A group of `+ - * / %` and comparisons gets one operand type, decided in order by
([checked] `crates/elab/src/numbers.rs:5-11`, the code at `numbers.rs:441-547`):

1. the expected type (`numbers.rs:441`);
2. a prefix `-` anywhere in the group, which forces `Int` (`numbers.rs:468-482`; a `Nat`
   expected type with a `-` is the "negative `Nat`" error);
3. pass 1: leaves with no numeric literal in them (or with a type ascription), inferred in order;
   the first with a numeric type decides (`numbers.rs:484-494`);
4. pass 2: the remaining leaves except bare literals (`numbers.rs:496-521`);
5. the first inferred numeric leaf, else a default of `Nat` (`numbers.rs:523-547`).

Step 2 runs before the leaves are looked at. On today's types that only shows up in error
messages (`s + -1` with `s: SafeInt` is a mismatch either way), but with `Float` it would make
`t + -1` an error for `t: Float`: the `-` would choose `Int` before `t` is seen. The review's
rule (D732): **collect the concrete type constraints first (the expected type, decimal or
exponent literals, typed operands), and only then let a unary `-` default an otherwise undecided
group to `Int`.** A known `Int` operand is still different from an untyped whole literal, so "no
mixing" stands.

**The new order**, with `Kind::Float` added:

1. **The expected type**, as today; it can now decide `Float`.
2. **New: a decimal or exponent literal** anywhere in the group decides `Float`.
3. **Pass 1, the typed operands**, as today's step 3: leaves with no literal in them, or with an
   ascription. `t` in `t + -1` decides `Float` here.
4. **Moved: the minus default.** If a prefix `-` occurs and nothing has decided yet, `Int`. If
   the group was decided as `Nat`, today's "negative `Nat`" error, worded for the decider (the
   expected type, or the leaf that made it `Nat`). If it was decided as anything else with a
   `-` (`Int`, `Float`), nothing happens: the `-` is that type's negation or subtraction.
5. **Pass 2 and the defaults**, as today's steps 4 and 5.

The minus default deliberately goes *before* pass 2, not after it: pass 2 infers leaves with
literals inside (`f 1`, `id 1`), whose literals would default to `Nat` on their own, so today's
`-(id 1)` (an `Int`) would become a negative-`Nat` error if pass 2 came first. The cost is that a
leaf with a literal inside doesn't count as a typed operand before the default: `-(Float.ofInt 5)`
with nothing else to decide is an `Int` group and a mismatch; an expected type or an ascription
fixes it. Groups with no `-` and no decimal literal take exactly today's path. Groups with a `-`
now have their pass-1 leaves inferred before the `Int` default rather than checked against `Int`;
I expect every group accepted today to get the same type, and the only visible changes to be which
error a rejected `Nat` or other-type group with a `-` reports [inferred: pass 1 skips the leaves
that need an expected type (`hopeless`, `numbers.rs:490`); the existing numeric-group tests are
the real check, in stage 1a step 2].

- **A whole literal in a `Float` group is a `Float`** (exactly, or refused as in §2.3).
- **A negative literal `-k` at `Float` is `Float.neg (k as Float)`**, so `-0` is `-0.0`, as in JS.
  (At `Int`, `-0` is `OfNat 0`, [checked] `numbers.rs:98-100`; that stays.)
- **No mixing:** `t + i` with `t: Float`, `i: Int` is the existing mismatch error; the fix is
  `t + Float.ofInt i`.

| Expression | Type | Value | Why |
|---|---|---|---|
| `-1 + 0.5` | `Float` | `-0.5` | step 2 (decimal literal) decides `Float` before the minus default |
| `0.5 + -1` | `Float` | `-0.5` | same group; `-1` is `Float.neg 1.0` |
| `def x: Float := -0` | `Float` | `-0.0` (bits `0x8000000000000000`) | expected type, then `Float.neg 0.0` |
| `-0`, otherwise unconstrained | `Int` | `0` | unchanged: the minus default |
| `t - 1000` (`t: Float`) | `Float` | | the leaf decides; `1000` is exact |
| `t + -1` (`t: Float`) | `Float` | `t + -1.0` | pass 1 decides from `t` before the minus default |
| `-1 + t` (`t: Float`) | `Float` | | same; leaf order doesn't matter |
| `-1 * t` (`t: Float`) | `Float` | | same |
| `-t` (`t: Float`) | `Float` | `Float.neg t` | same |
| `t + i` (`t: Float`, `i: Int`) | error | | `t` decides `Float`; `i` mismatches |
| `t + (-i)` (`t: Float`, `i: Int`) | error | | same; the `-` doesn't make the group `Int` |
| `1.5 * n` (`n: Nat`) | error | | `Float` vs `Nat` mismatch; write `Float.ofNat n` |
| `-(Float.ofInt 5)`, unconstrained | error | | the leaf has a literal inside, so the minus default comes first; write `(-(Float.ofInt 5): Float)` |

**Why a new kind rather than `Add`/`Mul` instances:** those interfaces carry laws (`zeroAdd`,
`assoc`, `comm`, [checked] `crates/elab/src/std/core/AddMul.sw:9-25`), and doubles break them:
`(0.1 + 0.2) + 0.3 ≠ 0.1 + (0.2 + 0.3)`, and `0.0 + -0.0` is `0.0`, not `-0.0` [run]. `-`, `/`
and `%` exist only on `Nat` and `Int`. So `Float`'s arithmetic operators go straight to
`Float.add` and the rest, as `Int`'s do when no dictionary applies ([checked]
`numbers.rs:843-873`). Comparisons need nothing new (§4).

- `/` and `%` on `Float` need **no** proof that the divisor isn't zero: `1.0 / 0.0` is `Infinity`
  and `0.0 / 0.0` is NaN, as in JS.
- **Evaluation order and grouping are kept**: the group builds the term with every leaf in place
  ([checked] `numbers.rs:9-11`), and `a + b + c` is `(a + b) + c` as in JS [inferred from the
  left-associative grammar]. An analysis of the app measured, with Node, on 100,000 random
  two-decimal millisecond values, that `(t - s) + s = t` fails 16,766 times and that `a + (b - c)`
  and `(a + b) - c` differ 42,082 times [reported by the port analysis]. Nothing in the compiler
  may reassociate (§3.3, C5).

### 2.5 Conversions and rounding (D687)

| Function | Type | Meaning |
|---|---|---|
| `Float.ofInt`, `Float.ofNat` | `Int -> Float`, `Nat -> Float` | nearest double, ties to even, like `Number(bigint)` [cited by the review]; ±∞ beyond the range. A primitive (it rounds) |
| `SafeInt.toFloat`, `SafeNat.toFloat` | `SafeInt -> Float` … | exact: every safe integer is a double |
| `Float.toInt` | `Float -> Option Int` | `Some` of the integer the double represents when it is finite and whole, else `None`. Total, and computable in the kernel too, being a definition; the `Option` is the checked result. **An ordinary definition over the bits**, with a native |
| `Float.toSafeInt`, `Float.toSafeNat` | `Float -> Option SafeInt` … | `toInt`, then the safe-range check |
| `Float.trunc`, `floor`, `ceil`, `round` | `Float -> Float` | as JS `Math.*` |

**`toInt` over the full range.** The result is an unbounded `Int`, so it covers every finite whole
double, not just those in `i64`: `Float.toInt 1e100` is the integer 1e100's bits represent,
`10000000000000000159028911097599180468360808563945281389781327557747838772170381060813469985856815104`,
which is not 10^100 (`BigInt(1e100) === 10n ** 100n` is false) [run]. The JS lowering is
`Number.isInteger(x) ? BigInt(x) : undefined`, which uses the represented value, never the display
string [inferred from the spec as cited by the review]. As a definition: split the bits into sign,
exponent `e` and fraction `f`; `e = 2047` is `None`; `e = 0` is `Some 0` if `f = 0` (both zeros),
else `None` (subnormals are below 1); otherwise `m = 2^52 + f` scaled by `2^(e - 1075)`, `None` if
that leaves a fraction. A dozen lines over `Nat` division and powers; it is exact bit decoding, not
rounding, so it needs no primitive, and the trusted base shrinks by one function.

`toInt (-0.0)` is `Some 0`: `Int` has one zero, so going through `Int` deliberately loses the
zero's sign (`Float.ofInt 0` is `0.0`).

**`round` is JS `Math.round`, all of it.** The ECMAScript rule [cited by the review, MDN cited]:
NaN, ±∞ and ±0 are returned as they are; `0 < x < 0.5` gives `+0`; `-0.5 <= x < 0` gives `-0`;
otherwise the integer nearest `x`, a tie going towards +∞. The usual shortcut `floor(x + 0.5)` is
wrong in three ways, all checked in Node [run]:

| `x` | `Math.round(x)` | `Math.floor(x + 0.5)` | Rust `x.round()` |
|---|---|---|---|
| `0.49999999999999994` | `0` | `1` (the sum rounds up to 1) | `0` |
| `-0.5` | `-0` | `0` | `-1` |
| `-0` | `-0` | `0` | `-0` [inferred] |
| `4503599627370497` (2^52 + 1) | `4503599627370497` | `4503599627370498` | same as `x` [inferred] |
| `-2.5` | `-2` | `-2` | `-3` [run] |

So the native is written to the specification's case split (and `|x| >= 2^52` returns `x`, since
every such double is whole), not built from `floor` or Rust's `round`. All five rows are tests.

`Float.ofText` is left for when a program parses text.

### 2.6 Printing (D688)

`Show Float`'s `toText` is JS `String(x)`, because a ported template `` `${t}` `` prints that:
`0.30000000000000004`, `1e+21`, `1e-7`, `NaN`, `Infinity`, and `-0` prints as `0` [run]. Rust's
`{}` differs on four of these [run], so the Rust runtime uses the `ryu-js` crate, a Ryū port that
follows ECMAScript's `Number::toString`, as used by the Boa engine [cited].

**`toText` is opaque, with a backend-supplied meaning (D688).** Unlike arithmetic, comparisons,
conversions, the constructor and the projections, `toText` has no shared concrete semantics
(§3.3). It is a bodyless primitive with no reduction rule. Each backend (the Rust runtime, the
generated JS) supplies its interpretation, which must be a pure, deterministic function of the
value under α (so all NaNs print alike, and `-0.0` and `0.0` may print differently or not, as
`String` does). Stage 1 does **not** promise identical strings across runtimes: `ryu-js` and a
conforming JS engine may differ (§3.6). Proofs that use `toText` are valid for every such
interpretation, because they can't see inside it; they can't show that two differing runtime
strings are the same string.

**What that costs in the kernel.** `Float.toText 0.5 = "0.5"` is not provable by `rfl`, and the
kernel evaluator that runs `test` declarations ([checked] `crates/driver/src/driver.rs:899`) gets
stuck on `Float.toText 0.5`. Not only in tests about printing: any kernel computation that
*consumes* the string gets stuck too, such as using it as a `Map` key, matching or branching on
it, or comparing it with `==`, and so does `Show` on any structure containing a `Float` (lists,
records, `Option`, which print their elements with `toSource`, [checked]
`crates/elab/src/std/core/Show.sw:120-130`). Tests of printing are Rust and Node tests (§7.4). If
a ported program uses numeric formatting as part of its algorithm (a key built from
`` `${t}` ``), the differential tests on the supported engines are the evidence for that
behaviour, not a kernel test. `stitchwort run` uses the Rust runtime ([checked]
`crates/driver/src/run.rs:328-332`), so programs still print floats.

**Totality vs kernel executability.** `Float.toText 0.5` is total in the sense of DESIGN.md's
totality statement ([checked] `DESIGN.md:138`: evaluating a closed, checked, assumption-free term
reaches a value): the runtime's evaluation does reach a `Text`. It is not *kernel-executable*: in
the checker its normal form is the neutral `Float.toText 0.5`, not a text constructor. The same
holds for every float primitive applied to a neutral argument, but only `toText` (and what calls
it) stays neutral on closed arguments. Docs that describe Stitchwort as total (DESIGN.md §3,
docs/core.md) get one sentence saying so when stage 1b adds `toText`.

**`toSource` (D733)** is not compiler tooling: it is the second field of the `Show` interface
([checked] `crates/elab/src/std/core/Show.sw:29-31`), used by `Show` on lists, options and pairs.
So it is specified here. `Float.toSource` is an **ordinary Stitchwort definition**, not a new
primitive:

- NaN → `"Float.nan"`; +∞ → `"Float.infinity"`; −∞ → `"-Float.infinity"`; `-0.0` → `"-0.0"`
  (decided from the bits, so these four reduce in the kernel);
- otherwise `Float.toText x`, with `".0"` appended when it contains neither `.` nor `e`
  (`3` → `"3.0"`, `1e+21` and `0.5` unchanged).

Its contract is the one `toText` gives it plus a guarantee that holds on every backend: the result
reads back, as a Stitchwort literal or expression, as the same `Float`. That needs only that
`toText` produce a decimal that rounds to `x`, which `Number::toString` requires of every
conforming engine and `ryu-js` does [cited by the review for the spec; the read-back of each output
is in §7.4]. Like `toText`, it is stuck in the kernel on finite non-zero values.

## 3. Semantics in the kernel, the runtime and JS

### 3.1 How natives work today

`Nat` is defined as `Zero | Succ Nat` but stored as one big number, `Term::Nat` / `Value::Nat`
([checked] `crates/core/src/term.rs:89-90`, `value.rs:28-29`). Some prelude definitions have
native implementations used when their arguments are numbers; the native must compute exactly
what the definition does, and the natives are trusted ([checked] `crates/core/src/native.rs:1-17`).
Natives can be switched off (`n0` in the test cache's modes, [checked]
`crates/driver/src/driver.rs:655-660`), and then the definitions unfold. The runtime and the JS
backend bind their own representations and operations to declarations **by content hash**:
`SafeNat` crosses as `number` only if its hash is `SAFE_NAT_HASH` ([checked]
`crates/rt/src/natives.rs:280`). The kernel already admits **bodyless definitions** for one
feature: `Delay`'s constants, "admitted here once their types are checked to be exactly these",
with a consistency argument ([checked] `crates/core/src/partial.rs:15-29`).

### 3.2 The choice (D681)

A rounding operation can't have an honest short Stitchwort definition: `+` on doubles is "add
exactly, then round to nearest-even", which needs the IEEE model. Three options:

- **(a) Fully opaque.** `Float` and all its operations are bodyless primitives; equality and
  comparison become axioms, as in Rocq and F\* [cited].
- **(b) Full model now.** Define every operation over the bits, as Lean does [cited]: a software
  floating-point library written and checked in Stitchwort, far more than the port needs.
- **(c) Bits model, rounding operations bodyless (D681, approved by the review).** The type is the
  record of §2.2. Everything exact and short is a definition over the bits: `DecEq`, `Ord`, the
  IEEE comparisons, `neg`, `abs`, `isNaN`, `isFinite`, `toInt`. These get natives bound by hash.
  The rounding operations (`add`, `sub`, `mul`, `div`, `rem`, `floor`, `ceil`, `trunc`, `round`,
  `ofInt`, `ofNat`) are bodyless primitives with fixed types, admitted like `Delay`'s constants,
  with the reduction rule of §3.4. `toText` is a bodyless primitive *without* a reduction rule.

What (c) costs in trust, stated precisely: **no new propositional axioms** (equality and order are
proved, not assumed), but **new trusted reduction rules**. A theorem proved by `rfl` through
`Float.add` depends on the Rust implementation of that rule being right. Replacing a primitive with
a checked definition later (§6.3) would improve assurance even if every result stayed the same.

Consistency [inferred, the review agrees]: interpret each primitive as the function on valid bit
patterns that the IEEE operation computes, with NaN results made canonical. That is a total
function, so the theory with these constants has a model, as the `Delay` argument does. Note what
this does *not* cover: a deterministic but numerically wrong implementation would also be
consistent. Agreement with IEEE and with the backends is the contract of §3.3, enforced by tests.

### 3.3 The trust contract

Three claims, kept apart:

1. **Consistency** of the logic with the primitives (§3.2).
2. **Agreement** of the reduction rules with IEEE 754 binary64.
3. **Preservation** of those semantics by the Rust runtime and the generated JS.

**The commuting equation.** Let α read a run-time double's binary64 representation, keep signed
zero, and map every NaN to the canonical NaN. α is extended to every argument and result type in
the obvious way: the identity on `Bool` and `Nat` (`.bits`, the comparisons), the run-time `Int`
to the logical `Int`, componentwise on `Option` (`toInt`), on `Decidable` its constructor (`Yes`
or `No`; proofs are erased), and the identity on proofs. For each operation `op`, with `modelOp`
the kernel's meaning (the reduction rule, or the definition over the bits):

> α(runtimeOp(x₁, …, xₙ)) = modelOp(α x₁, …, α xₙ)

for the kernel evaluator (native and WASM builds), the Rust runtime and the generated JS. It
governs arithmetic, conversions, the record constructor and `.bits`, `DecEq`, `Ord`, the IEEE
comparisons, hashing of values, and constant folding. §7.4 tests it, path by path.

**`toText` is the exception.** It has no `modelOp`: it is opaque, and each backend supplies its own
interpretation, constrained only to be pure, deterministic and to respect α (§2.6). The equation
above is the shared semantics of everything else.

**Execution conditions.** The equation is promised only when:

- **C1** binary64 arithmetic rounds to nearest, ties to even (the IEEE default; also what JS
  specifies [unverified]);
- **C2** subnormals are kept (no flush-to-zero or denormals-are-zero);
- **C3** signed zero is kept by every operation and every lowering;
- **C4** NaN results are made canonical wherever they are observed (D701);
- **C5** no reassociation, no algebraic simplification (`x + 0.0 → x` is wrong for `-0.0`) and no
  contraction of `a * b + c` into a fused multiply-add, in the compiler's optimiser, in the Rust
  code it is built from, and in generated JS. Rust doesn't contract floating-point expressions
  without explicit `mul_add` [unverified]; `crates/rt/src/opt.rs` does constant propagation and
  beta only ([checked] `opt.rs:1-30`); JS engines must not, by the language's semantics
  [unverified]. Tests pin both (§7.4);
- **C6** the host's floating-point environment is the default one: nothing (FFI, a host
  embedding the WASM kernel) changes the rounding mode or the flush-to-zero flags. Lean qualifies
  its own guarantee the same way [cited by the review].

On x86-64 and aarch64 with Rust's defaults, C1–C3 hold by default [unverified]; WASM specifies
round-to-nearest and subnormals and leaves only NaN bits nondeterministic [cited].

**Reduction on values, not syntax.** See §3.4: whether `x + y` computes depends on what `x` and
`y` evaluate to, never on whether a literal was written there.

**Primitive identity.** An ordinary definition's hash leaves out its own name ([checked]
`crates/core/src/hash.rs:29-30`), so two bodyless primitives of the same type, `add` and `sub`,
would hash the same. `Delay`'s constants already avoid this: a primitive is hashed as the tag
`primitive`, its name and its type ([checked] `hash.rs:96-104`). The float primitives do the
same, with the name as the operation tag, and add the contract version below.

**A versioned semantic contract.** The table of primitives, their types and the reduction rules'
meaning (this section, §2.5 and §3.6) is version `FLOAT_CONTRACT = 1`, a constant in `core`, hashed
into every float primitive's hash. A deliberate change of meaning (say, a different `round`) bumps
it: every primitive's hash changes, so every definition using one changes hash, and the runtime's
and JS's hash bindings fail their test until re-checked ([checked] the pattern at
`crates/cli/tests/extract.rs:1979-1989`).

**Caches.** What the caches key on today:

- The **check cache** key includes the entry format `FORMAT` ([checked]
  `crates/elab/src/cache/mod.rs:66-68`), the compiler string `stitchwort-{version}-{FINGERPRINT}`
  ([checked] `crates/driver/src/check_cache.rs:51`), and the directory's salt; each entry lists its
  dependencies with the content hashes they must have ([checked] `cache/mod.rs:70-72`).
- The **test cache** key is `{COMPILER}-{FINGERPRINT}-{modes}-{test hash}` ([checked]
  `driver.rs:712`).
- `FINGERPRINT` is a BLAKE3 hash of the sources of `syntax`, `core`, `elab` and `driver`, and of
  `Cargo.lock` ([checked] `crates/driver/build.rs:16-53`).

So a fix to a reduction rule in `core` already changes the fingerprint and empties both caches,
and a new `ryu-js` or other crate version does too, through `Cargo.lock`. What changes:

1. **The reduction rules live in `core`** (fingerprinted), not in `rt` or `js`, which aren't
   ([checked] `build.rs:16`).
2. **Add the Rust toolchain and target to the fingerprint.** Literal parsing is the standard
   library's `str::parse::<f64>`, and the f64 operations are compiled by the toolchain; neither is
   in any hashed source or in `Cargo.lock`. `build.rs` runs `$RUSTC -vV` and reads `TARGET`, and
   hashes both. A cache directory is never shared between a native and a WASM build anyway (the
   salt, [checked] `check_cache.rs:9-11`), so adding the target costs nothing.
3. **`FLOAT_CONTRACT` in the primitives' hashes**, as above: a semantic change invalidates by
   hash, independently of the build.
4. **The float reduction rule ignores the natives switch.** With natives off, a native's
   definition unfolds; a primitive has none, so if the rule were a "native" it would make `rfl`
   proofs depend on the mode. It is part of the kernel's evaluation, always on. The definitions
   over the bits (`DecEq`, `Ord`, `neg`, `toInt`) are ordinary natives and do switch off; §3.4
   says what they must agree on for that to be invisible.

### 3.4 What the checker does with `1.5 + 2.0` (D682)

It **computes**, natively. When a float primitive is applied to all its arguments, the evaluator
forces each `Float` argument; if each is a record whose `bits` field forces to a number, it
converts the bits to `f64`, applies the Rust operation, makes a NaN result canonical, and returns
`{ bits = k, valid = Eq.refl True }`. Otherwise the application is stuck (a neutral term), and
conversion compares stuck applications structurally, as it does for `Delay`.

- **Values, not syntax:** a literal, a named constant (`def half: Float := 0.5`), and a record
  whose `bits` is computed (`{ bits = 2 * k, valid = … }` with known `k`) all reduce. Two
  terms that evaluate to the same double behave the same.
- **A typed result:** `Float.isValid k` for a number `k` evaluates to `True`, so
  `Eq.refl True : Float.isValid k = True` checks by conversion. The literal elaborator builds
  exactly the same record, so `0.1 + 0.2` and the literal `0.30000000000000004` are the same
  value and `rfl` proves them equal. A debug assertion and a test evaluate `isValid` on every
  result.

A `Float` value in the kernel is just the record with a `Nat` literal inside; no new `Value`
variant is needed. The pretty-printer shows a `Float` record with literal bits as its literal
(`1.5`), so goals stay readable.

**Two different kinds of "the same Float".** The kernel has no definitional proof irrelevance, so
two records with the same bits and different `valid` proofs are distinct normal forms. That gives
two separate questions, with separate answers.

*Propositional: bit extensionality.* Equal bits make equal `Float`s:

```
theorem Float.bitsExt (x: Float) (y: Float) (e: x.bits = y.bits): x = y
```

The `valid` proofs are proofs of `Float.isValid n = True`, an equation between `Bool`s, and
`Bool` equations have unique proofs (`Bool.uniqueEq`, [checked]
`crates/elab/src/std/core/Decidable.sw:123`; the general fact is uniqueness of identity proofs for
types with decidable equality, as in Rocq's `Eqdep_dec` [cited by the review]). So `bitsExt` is
`SafeNat.ext`'s proof with `isValid` in place of the bound ([checked]
`crates/elab/src/std/Int/Safe.sw:26-37`; `Char` does the same, `crates/elab/src/std/core/Char.sw:26`).
No new axiom. It is used by: `DecEq Float` (a successful bit comparison becomes `x = y`), the
injectivity proof of the total-order key (§4.5), and proofs such as `neg (neg x) = x` whose two
sides may carry different witnesses. It says nothing about normal forms: `rfl` can't use it.

*Definitional: natives agree with their definitions, proof fields included.* An ordinary native
(the exact definitions over the bits: `neg`, `abs`, `isNaN`, `DecEq Float`'s `decide`, `toInt`, …)
must compute exactly what its definition computes, **as a whole term up to conversion, proof
fields included**, so that turning natives off never changes which `rfl` proofs check. This is
already the rule for the `Nat` natives ([checked] `crates/core/src/native.rs:13-17`, and
`eqNatSound` returns `rfl` "whatever `h` is", `native.rs:64-67`). For `Float` the requirement
reads: **for an exact operation whose result is a `Float` (or contains one, or a proof about one),
when the relevant bits are known, the source definition and its native produce definitionally
equal records.** The primitive reducer and the literal elaborator already produce
`{ bits = k, valid = Eq.refl True }`; the question is whether the definitions do.

The risk is concrete. Given `p : Float.isValid k = True` as a variable and
`x := { bits = k, valid = p }` with `k` known, an `abs` defined to return `x` itself when the sign
is clear unfolds to a record whose `valid` is `p`, a neutral term; a native that reads `k` and
rebuilds `{ bits = k, valid = Eq.refl True }` differs from it. And `1.0 - 2.0 = -1.0` compares a
primitive's result with `Float.neg 1.0` (the elaboration of `-1.0`, §2.4), which with natives off
is whatever `neg`'s definition builds.

**The approach (D731): one checked constructor, and natives only where they reproduce it.**

1. Every exact definition that returns a `Float` builds it with `Float.make n p` (§2.2), never by
   returning an argument or writing a record literal. `Float.make`'s witness is
   `Bool.canonicalTrue (Float.isValid n) p`, which reduces to `Eq.refl True` as soon as
   `Float.isValid n` reduces to `True`, that is, whenever `n` is known and valid, *whatever `p`
   is*. So on known bits the definition, the native, the primitive reducer and the literal
   elaborator all produce `{ bits = k, valid = Eq.refl True }`.
2. A `Float`-returning native fires only when the bits it needs are known numbers (as the `Nat`
   natives fire only on numbers), and then returns exactly that record. On unknown bits it doesn't
   fire and the definition unfolds, so there is nothing to disagree about. It also doesn't fire
   on known bits that fail `isValid` (possible only under an absurd hypothesis `p : Float.isValid
   k = True`, where `Float.make`'s witness would be `p` itself, not `Eq.refl True`).
3. A native returning a proof or a proof-carrying value (`DecEq Float`'s `Yes`/`No`) returns the
   proof term the definition computes, as `decEqNat`'s native does ([checked] `native.rs:58-60`,
   `130-132`). If the definition's proof term is awkward to reproduce, the native is restricted
   (to the `Bool`-valued helper it calls, for example) or left out of the kernel entirely: the
   runtime and JS implementations don't depend on it, and the kernel only loses speed.
4. A native whose agreement isn't shown by the checks below is not enabled in the kernel.

**Acceptance checks.** Each is run with ordinary natives on and off (the `n0` mode, [checked]
`crates/driver/src/driver.rs:655-660`), on the native and WASM kernels, and compares the
**conversion or normal forms of the whole terms**, not `.bits` and not a `DecEq` result, either
of which would hide a proof-field difference.

| Check | Establishes |
|---|---|
| `rfl : 0.5 + 0.25 = 0.75` and `rfl : 0.1 + 0.2 = 0.30000000000000004` | positive primitive result vs positive literal (the shared witness) |
| `rfl : 0.0 + (-1.0) = -1.0` and `rfl : 1.0 - 2.0 = -1.0` | primitive result vs negative literal (the `Float.neg` elaboration path) |
| with `p : Float.isValid k = True` a variable and `k` a known valid number: `Float.neg { bits = k, valid = p }` and `Float.abs { bits = k, valid = p }` normalise to `{ bits = k', valid = Eq.refl True }` | native vs definition beyond literal inputs, with a neutral witness |
| `Float.neg (Float.neg 1.5)` normalises to the literal `1.5`; `neg` of NaN normalises to `Float.nan` | the `Float.make` path through two calls, and the NaN case |
| `DecEq Float`'s `decide` on equal and on different known values: the same `Yes`/`No` term with natives on and off | proof-carrying native results |

**This is the first gate of stage 1a** (§7.2): it is built and passing before the runtime, JS or
boundary work starts, because if it fails the fix is in the definitions' shape, which everything
else builds on.

### 3.5 Run time and the representation invariant (D701)

The first review asked for one of two run-time invariants: (1) every stored `Float` is physically
canonical; (2) values may hold any NaN, and every representation-sensitive operation handles them
canonically. The decision is **(1) wherever Stitchwort owns the representation, and in JS (2)
with all bit reinterpretation in one audited module**:

- **Kernel:** canonical by construction (the record's `valid` field; the reducer canonicalises).
- **Rust runtime (`crates/rt`):** a new `Value::Float(f64)`, next to `Value::Nat`/`Int`/`Text`
  ([checked] `crates/rt/src/value.rs:21-42`), built only through one constructor that maps any NaN
  to `f64::from_bits(0x7FF8000000000000)`. One `is_nan` test per result is cheap, and it means
  native `DecEq` can compare `to_bits()`, native `Ord` can use the bits' key (not raw
  `f64::total_cmp`, which puts negative NaNs before `-∞`: `total_cmp(-NaN, -∞)` is `Less` [run],
  while the model's one NaN is greatest), and hashing is of the bits. The record is replaced by the
  `f64` when `Float`'s hash matches `FLOAT_DATA_HASH`; `.bits` and the constructor become natives.
- **JS:** a `Float` is a `number`, and canonicalising every result (`x !== x ? NaN : x`) would cost
  a test per operation for nothing observable. JS code can see a NaN's bits only through typed
  arrays and `DataView` [inferred]; `===`, `<`, `Object.is`, `Map`, `Set` and `String` treat all
  NaNs alike (`Object.is` of a negative-payload NaN and `NaN` is true, and the payload survives
  `* 1` in Node) [run]. So JS is invariant (2). Bit reinterpretation is needed in two directions,
  not one: `.bits` observes an existing number's representation, and the **dynamic record
  constructor** `{ bits = b, valid = p }` (with `b` computed at run time) must turn `b` into the
  double it encodes, which `Number(b)` would not do. (Constant literals need neither: they are
  emitted as short decimal spellings, §2.3.)

  **One audited module** in the JS runtime prelude holds every Float bit reinterpretation:

  ```
  toCanonicalBits(x: number): bigint      // the binary64 pattern, any NaN as 0x7FF8000000000000
  fromCanonicalBits(b: bigint): number    // b a valid canonical pattern (Float.isValid b)
  ```

  with two laws: `toCanonicalBits(fromCanonicalBits(b)) === b` for every valid canonical `b`, and
  `Object.is(fromCanonicalBits(toCanonicalBits(x)), x)` for every JS number `x`. Then `.bits` is
  `toCanonicalBits`; the dynamic constructor is `fromCanonicalBits`; the total-order key (`Ord`)
  and value hashing, if the JS backend ever hashes, use `toCanonicalBits`. Lawful `DecEq` lowers to
  `Object.is`, which is NaN-blind and needs neither. The `Float64Array`/`BigUint64Array` (or
  `DataView`) code lives only in this module; a test fails if either appears anywhere else in the
  runtime prelude or generated code, and property tests check the two laws on the §7.4 edge set,
  random patterns and several NaN payloads. The audit rule is "all Float bit reinterpretation goes
  through this module". The Rust runtime has the same pair (`to_bits` with the canonicalising
  constructor, `from_bits`), already canonical by construction.

**Scope of the guarantee:** propositional equality corresponds to the value abstraction α
(`Object.is`, one NaN). Stitchwort does not promise to preserve arbitrary NaN payloads that
external code sets through typed arrays.

The alternative, (2) in the Rust runtime too, saves one branch per operation and adds the audit of
every native that looks at a double's representation. (1) in JS as well is possible but costs on
every operation.

### 3.6 Do Rust and JS agree?

| Operation | Agree? | Evidence |
|---|---|---|
| `+ - * /`, `sqrt` | yes: correctly rounded IEEE binary64 in both | JS spec's Number::add etc. [unverified]; ECMAScript 2026 requires correctly rounded `Math.sqrt` [cited by the review]; Rust: `sqrt` "guaranteed to be the rounded infinite-precision result" [cited]; `0.1 + 0.2` and `80281.87 - 80000` print identically [run] |
| `%` | yes: truncated remainder, which is exact | `5.5 % 2` = `1.5`, `-5.5 % 2` = `-1.5` in both [run] |
| `floor`, `ceil`, `trunc`, `abs` | yes: exact | Rust: "always returns the precise result" [cited] |
| `neg` | the value yes; NaN bits no | Rust's `-NaN` is `0xFFF8…` [run]; canonicalised by D701 |
| `round` | **no**: Rust goes away from zero | §2.5 table [run]; the native implements JS's rule |
| comparisons | yes (IEEE) | [inferred] |
| total order | **not with `f64::total_cmp`** on raw NaNs | [run]; D701 |
| NaN bits | **no guarantee**: Rust: "nothing is guaranteed about the specific bit pattern … both payload and sign are arbitrary" [cited]; WebAssembly leaves NaN bits nondeterministic [cited]; x86 produces a negative NaN for `0/0` [unverified]; on arm64 Rust's `0/0` gave `0x7FF8000000000000` [run] | D701 |
| `toText` | **not guaranteed**: `Number::toString` picks the digit count `k` as small as possible, but when several `k`-digit decimals round to `x`, choosing the closest (ties even) is only a recommendation in a note [cited by the review]. `ryu-js` picks the closest; an engine may conform and differ | the kernel doesn't reduce `toText` in stage 1 (D688) |
| literal parsing | Stitchwort defines it (correctly rounded); JS may round past 20 significant digits differently | §2.3: JS is generated from the bits, so the engine's literal parser only sees short round-trip spellings |
| `pow`, `exp`, `log`, trig | **no**: Rust: "precision … is non-deterministic" [cited]; JS engines differ [unverified] | **excluded** from stage 1 |

**On `toText` (D688):** the first review's three options are to test and specify supported
engines, to use one formatting algorithm everywhere (so JS would call a Stitchwort formatter, not
`String(x)`), or to keep `toText` from reducing in the kernel. The decision is the third for stage
1, approved by the second review (opaque, backend-supplied, §2.6): the
port needs `String(x)` at run time, not proofs about strings, and the first two are each a project
(an engine conformance suite, or a JS formatter that would also have to match `String(x)` to keep
ported templates identical). Unlocking it later is a one-rule change once a contract is chosen.

`sqrt` is correctly rounded in both, so it can join later without a decision. `min`/`max` can too,
but they must be written to JS's rules (`Math.min(0, -0)` is `-0`, NaN wins), not taken from
Rust's `f64::min`, which returns the non-NaN argument [unverified].

## 4. Equality and ordering (D683, D684)

### 4.1 The decision

Draft 1 made `==`, `!=`, `<`, `<=` on `Float` mean JS's IEEE comparisons. **Draft 2 keeps them
lawful, as on every other type**, and gives JS's comparisons names:

| Stitchwort | Meaning on `Float` | JS equivalent |
|---|---|---|
| `a == b`, `if h: a = b`, `a = b` | `DecEq Float`: the same double | `Object.is(a, b)` |
| `a != b` | `Not (a = b)` ([checked] `crates/elab/src/numbers.rs:617-620`) | `!Object.is(a, b)` |
| `a < b`, `a <= b` | `Ord Float` (IEEE `totalOrder`), through `Std.Ord.lessThan`/`lessEq` ([checked] `numbers.rs:854-855`) | none |
| `Float.ieeeEq a b` | `Bool`: IEEE equality | `a === b` |
| `Float.ieeeLt a b`, `Float.ieeeLe a b` | `Bool`: IEEE comparisons | `a < b`, `a <= b` |

A port writes JS's `a === b` as `Float.ieeeEq a b`, `a !== b` as `!Float.ieeeEq a b`, `a > b` as
`Float.ieeeLt b a` and `a >= b` as `Float.ieeeLe b a`, evaluating `a` before `b` when they are
not plain values (§6.4 item 5). Not `!Float.ieeeLt a b` for `>=`: with NaN,
`!(a < b)` and `b <= a` differ, as in JS [inferred from IEEE]. The three are definitions over the
bits, so lemmas such as `Float.ieeeLt a b = True -> Float.ieeeLe a b = True` are provable.

This needs no special case in `numbers.rs` for comparisons: `==` already goes to `DecEq` and `<` to
`Ord` for any type with instances ([checked] `numbers.rs:603-633`, `843-873`).

### 4.2 Why: the refactoring examples

If `==` and `<` were IEEE on `Float` alone, they would disagree with the generic route through
`DecEq` and `Ord`, and ordinary refactorings would change behaviour (the review's examples):

```
def same [auto eq: DecEq a] (x: a) (y: a): Bool := x == y
def genericLess [auto ord: Ord a] (x: a) (y: a): Prop := x < y
```

| Draft 1 (IEEE operators) | Value | Generic equivalent | Value |
|---|---|---|---|
| `0.0 == -0.0` | `True` | `same 0.0 (-0.0)` | `False` |
| `Float.nan == Float.nan` | `False` | `same Float.nan Float.nan` | `True` |
| `0.0 == -0.0` | `True` | `{ time = 0.0 } == { time = -0.0 }` (derived `DecEq`) | `False` |
| `-0.0 < 0.0` | false | `genericLess (-0.0) 0.0` | true |

Extracting a helper or wrapping a value in a record are refactorings no one expects to change a
branch. And as propositions, draft 1 made both `Float.nan = Float.nan` (true, by `rfl`) and
`Float.nan != Float.nan` (IEEE) hold, so `!=` stopped being `Not (=)` on one type.

Lean can make `==` IEEE because its `BEq` promises nothing (`LawfulBEq` is separate) [cited by the
review]. Stitchwort's `==` is defined as `DecEq`'s decision ([checked] `DecEq.sw:5-12`), so it can
only be lawful. The other coherent route, lawless operator interfaces with lawful refinements, would
change every existing instance and isn't needed now.

With draft 2's rule, the four rows agree: `0.0 == -0.0` is `False` everywhere, `Float.nan ==
Float.nan` is `True` everywhere, `-0.0 < 0.0` holds everywhere. The cost moves to porting: JS's
`===` must be translated deliberately (§6.4), and a reviewer can see each translation.

### 4.3 Three equalities, for reference

| | `NaN` vs `NaN` | `0.0` vs `-0.0` | Lawful? | Stitchwort |
|---|---|---|---|---|
| IEEE (JS `===`) | not equal | equal | not reflexive; not a congruence (`1/0 ≠ 1/-0`) | `Float.ieeeEq` |
| Same double (JS `Object.is`) | equal | not equal | yes | `==`, `=`, `DecEq` |
| SameValueZero (JS `Map`, `Set`, `includes`) | equal | equal | not a congruence | none |

SameValueZero as `DecEq` would be sound only if nothing could tell `0` from `-0`, which division
can (`1/0` vs `1/-0`), so it is ruled out.

### 4.4 Keeping the choice through compilation

Elaboration resolves `==` to the `DecEq Float` instance's `decide` and `Float.ieeeEq` to its own
definition: different core definitions with different hashes. Inlining and specialisation may
replace a call by its body but never one definition by the other; the JS backend lowers the
`DecEq Float` native to `Object.is` and `Float.ieeeEq` to `===`, each bound by its own hash. §7.4
tests that a generic helper specialised to `Float`, after inlining, still distinguishes the zeros.

### 4.5 `Ord Float` (D684)

IEEE's `totalOrder` on the canonical bits: `-∞ < … < -0.0 < 0.0 < … < +∞ < NaN`. Built with
`Ord.byKey` from a key mapping the bits to an `Int` monotonically, with its injectivity proof
(the pattern at [checked] `crates/elab/src/std/Int/Safe.sw:67-69`). This is what `sort`, `sortOn`,
`Map Float`, `Set Float`, derived `Ord` and now `<` use. It is lawful, as `Ord` requires (`equal`,
`flip`, `trans`, [checked] `crates/elab/src/std/core/Ord.sw:32-34`). IEEE comparison can't be an
`Ord`: `equal` fails on `0.0`/`-0.0` and NaN breaks `flip`.

Two cautions, both from the review:

- **A total-order sort can differ from the original comparator's.** In JS,
  `[{id: "a", time: +0}, {id: "b", time: -0}].sort((a, b) => a.time - b.time)` gives `a, b`: the
  comparator returns 0, and `Array.prototype.sort` is stable [run]. `List.sortOn (r => r.time)`
  with `Ord Float` puts `-0` first: `b, a` [inferred from the order above]. Even with no signed
  zeros, "sorted permutation" doesn't fix the order of equal keys. A port therefore keeps the
  original comparator and stability (§6.4); `List.sortBy` takes any comparator and is stable
  ([checked] `crates/elab/src/std/List/Sort.sw:496-501`).
- **JS `Map` and `Set` use SameValueZero**: `new Map([[0, …]]).set(-0, …)` has one entry, and
  `new Set([0, -0, NaN, NaN])` has two [run]. Stitchwort's `Map Float` and `Set Float` keep `0.0`
  and `-0.0` apart. A future lowering of them to native JS collections needs canonical-bit keys
  (or an adapter), not raw numbers. This is a backend requirement, not a reason to weaken `Ord`.

## 5. The JS boundary (D685)

- **Type:** `number` in the `.d.ts`. `Option Float` is `number | undefined` (D582).
- **Decoding: every JS `number`**, including NaN, ±Infinity and `-0`; refuse anything else
  (`bigint`, strings), with the existing `refuse` messages. Every decoded NaN denotes
  `Float.nan`: observing its bits through Stitchwort (`.bits`, the total order, hashing) gives the
  canonical pattern. This is a statement about the logical value under α; the JS number itself
  is passed through and may keep whatever payload it had (§3.5).
- **Encoding:** the `number` itself.

Why draft 1's refusal of NaN and ±Infinity is dropped: `Float`'s values include them, so a decoder
that refuses them restricts the type rather than enforcing it, and breaks composition. With
`export def makeInfinity (): Float := 1.0 / 0.0` and `export def identity (x: Float): Float := x`,
`identity (makeInfinity ())` works in Stitchwort but would throw at `identity`'s decoder from JS,
though both are typed `number`; so would storing an exported result and passing it back. `SafeNat`
is different: its decoder enforces the type's own invariant ([checked]
`crates/elab/src/std/Int/Safe.sw:1-14`).

Draft 1's JSON argument was also wrong. JSON has no `Infinity` literal, but `JSON.parse("1e400")`
is `Infinity`, and finite inputs don't give finite intermediates: `Number.MAX_VALUE +
Number.MAX_VALUE` is `Infinity` [run]. A proof or a compatibility argument that needs finiteness
needs an invariant over the computation, not a decoder check.

**Where finiteness goes (D702):** on the application's own types (a timeline's domain type checks
its times, with a proof of `Float.isFinite t = True` in a field if a theorem needs it), or on a
`FiniteFloat` refinement, `{ value: Float, finite: Float.isFinite value = True }`, crossing as a
checked `number` as `SafeNat` does. Decided: no `FiniteFloat` in stage 1. The port validates
at its own types; `FiniteFloat` joins std when a program wants the check at the boundary, so its
shape comes from use.

**An erased proof field checks nothing at run time.** In a record such as `{ time: Float, finite:
Float.isFinite time = True }` the proof field is erased, so no run-time code tests `isFinite`
because the field exists; only code that computes the proof does. So an application that needs
finite input must test finiteness on its decoding or validation path (`if h: Float.isFinite t
then … else reject`) before it builds the refined value; the type only records that the test was
made. `FiniteFloat`, when it comes, would be a checked codec like `SafeNat`'s, which is exactly
that test done at the boundary.

**The guarantee at the boundary** is about the value abstraction: a `number` that crosses in and
back out is the same value under `Object.is`. NaN payloads set by external typed-array code are not
preserved (§3.5).

- **Attributes** (docs/proposals/attributes.md): `Float` joins the special-codec types that reject
  `@[js.*]` attributes inside them ([checked] attributes.md:447), through the shared registry of
  D613.
- **Binding:** by content hash (`FLOAT_DATA_HASH`, one hash per primitive and per native
  definition), as `SAFE_NAT_HASH` is.

## 6. Proofs

### 6.1 What stage 1 can prove

- **Structural facts, directly about `Float` code.** The rounding operations are unknown functions
  to a proof, so anything that doesn't depend on what they compute is provable: the times `inWindow
  start end xs` returns are all in `xs`, each satisfies `start <= t` (in the total order) or
  `Float.ieeeLe start t = True`, whichever the code tests; `shiftAll d xs` has the same length as
  `xs`; a sort by `Ord Float` returns a sorted permutation.
- **Facts about the exact definitions:** `Float.bitsExt`, `neg (neg x) = x`, `abs` is
  non-negative in the total order, `ieeeLt a b = True -> ieeeLe a b = True`, `ieeeEq` is
  symmetric, and facts about the exact decoder `toInt` itself (`toInt x = Some n` implies `x` is
  finite; `toInt` of NaN and ±∞ is `None`; `toInt (neg x)` is the negation of `toInt x`).
- **Conversions, concretely only.** `toInt` and `ofInt` on known values compute (`Float.toInt
  1e100`, `Float.ofInt 0 = 0.0`, `Float.toInt (-0.0) = Some 0`), so concrete round trips are `rfl`
  proofs and tests. The general inverse relation is *not* promised in stage 1. Its correct
  statement excludes negative zero, since `toInt (-0.0) = Some 0` and `ofInt 0 = 0.0 ≠ -0.0`:

  ```
  Float.toInt x = Some n -> x ≠ -0.0 -> Float.ofInt n = x
  ```

  But `ofInt` is a bodyless primitive whose rule fires only on known integers, so for a symbolic
  `n` there is nothing to prove `Float.ofInt n` equal to from; the theorem needs a model of `ofInt`
  (§6.3), not more `Nat` bit lemmas. It is deferred until `ofInt` has one.
- **Facts about known doubles, by computation:** `0.1 + 0.2 = 0.30000000000000004` by `rfl`.
- **The limit:** stage 1 provides no practical general reasoning framework for rounded
  arithmetic. Congruence still works (`x = y -> x + z = y + z`), and the domain is finite, so
  exhaustive reasoning is possible in principle; but `t + 0.0 = t` (false anyway for
  `t = -0.0`) or bounds on `(t - s) + s` are out of practical reach.

A theorem should name its relation. A list sorted by `Ord Float` may contain NaN and still fail
adjacent `Float.ieeeLe` checks; "sorted" means sorted in the total order unless it says otherwise.

### 6.2 Programs over an operations record (D689)

Every theorem proved about the app uses only the code's own operations on times, never an
arithmetic law, and they were all checked **generic** over a record of operations with no laws,
plus `DecEq` on the time types [reported by the port analysis]:

```
-- `i` is an instant, `n` a length of time. Operations only: no laws.
type TimeOps (i: Type) (n: Type) =
  { zero: n, add: i -> n -> i, sub: i -> i -> n, endTime: i -> n -> i
  , le: i -> i -> Bool, lt: i -> i -> Bool, order: i -> i -> Ordering, duration: n -> n -> n }
```

Instantiated at `Float` as `ieeeTimeOps` (built from `Float.add`, `Float.sub`, `Float.ieeeLe`,
`Float.ieeeLt`, …, matching what the TS does), the theorems cover the exported code directly. A
lawless record is the shape, not an extension of `Add`/`Ord`, whose laws doubles break.

Where a property needs algebra, the laws are a **separate hypothesis**:

```
type TimeLaws (i: Type) (n: Type) (ops: TimeOps i n) =
  { subAdd: (t: i) -> (s: i) -> ops.add s (ops.sub t s) = t }
-- provable for the operations over `Int`; there is no value of `TimeLaws Float Float ieeeTimeOps`
```

The claim is about `ieeeTimeOps`, the IEEE `add` and `sub`. Other operations over `Float` could
satisfy the law (`sub t s := t` with `add s d := d`), so "no `Float` value exists" alone was wrong.
The theorem shows the algorithm is right over `Int`; it says nothing about rounding. `Nat` can't
supply `subAdd` (`-` stops at zero), and `SafeInt` has no closed `add` of its own [inferred].

Keep `TimeOps` in the ported module (approved): generalise it into std when a second program needs
one.

### 6.3 Later: the full model

Giving `add` and the rest definitions over the bits (Lean's route [cited]), or the
integer × 2^exponent view with exact-then-round (Flocq's [cited]), would make rounding-error
theorems possible and turn the primitives into ordinary natives. If those definitions compute the
same results, **source behaviour stays compatible**: every program means what it did. It is not
invisible: the primitives become definitions, so their hashes change, every dependent hash
changes, and caches and runtime bindings are rebuilt. Stage 1 doesn't block it.

### 6.4 Port verification obligations

A theorem that holds when a generic proof is instantiated at `Float` says the instantiated program
has the property. It doesn't say the program behaves like the TypeScript it was ported from. For a
ported TS program, that needs its own arguments:

1. **The equality behind each equality theorem.** If a theorem turns a successful Boolean list
   comparison into propositional equality, it needs the comparison to be `DecEq` (same double).
   Audit the original: what predicate did it use (`===`, a field-by-field helper, a library
   `isEqual`)? Can values that `===` identifies but `DecEq` doesn't (`0` and `-0`) reach it, or
   values that `===` separates (NaN)? Does the port use the same predicate? If the port
   intentionally uses a different one, does that change a returned value or a branch? Should the
   theorem be stated over the original relation instead? "TS has no structural equality" doesn't
   settle this: TS programs build structural comparisons from `===` on fields.
2. **Comparators, ties and stability.** Keep the original comparison function (translated with
   `ieeeLt`/`ieeeLe`, or as a comparator returning the sign of `a - b`, with NaN as a tie, as JS
   does), and stability or an equivalent original-position tie-breaker. Equal keys, signed zeros
   included, must come out in the original order (§4.5). If NaN can reach an inconsistent
   comparator, a different sorting algorithm may give a different result even with the same
   comparator; establish that NaN can't arrive, or scope the claim.
3. **Arithmetic order.** Keep the original grouping and order of operations used to produce keys
   and results (§2.4).
4. **Differential tests transport canonical bits.** Compare results by their canonicalised
   binary64 bits, `toCanonicalBits(a) === toCanonicalBits(b)` (§3.5), sent as hex or another
   lossless encoding, not through JSON or `===`, which hide `-0` vs `0` and turn NaN and ±Infinity
   into `null`. Canonicalisation changes only NaNs: every other pattern must match exactly, `-0`
   and `0` included. Apply the same canonicalisation to the original TypeScript program's results,
   or the oracle would reject NaN payload differences that D701 permits. Include signed-zero
   equality branches, duplicate times, stability and internally produced non-finite values.
5. **Comparison translation keeps evaluation order.** `a > b` becomes `Float.ieeeLt b a` and
   `a >= b` becomes `Float.ieeeLe b a`, but JS evaluates the left operand before the right even
   for these [cited by the review]. When the operands are expressions with effects (or that may
   not terminate, or are expensive), evaluate each once, left then right, and then reverse:
   `left() >= right()` becomes a block with `let l := left()`, then `let r := right()`, then
   `Float.ieeeLe r l`. For variables
   and pure expressions (timestamps already computed) the direct form is fine.

These are open obligations for each port, not evidence that a port is wrong.

## 7. Implementation, cost, risks, tests

### 7.1 By crate

| Crate | Work |
|---|---|
| `syntax` | `Tok::Float(text)`; no `Float` token right after `.`; AST literal keeps text; lexer and parser tests (`x.name`, `List.map`, `xs.0.1`, `[x, ..rest]` unchanged) |
| `core` | admission of bodyless float primitives with exact types and names (beside `partial.rs`); the reduction rule (forced arguments, canonical bits out, the standard witness), always on; `Float` natives for the exact definitions, firing only on known bits (§3.4); `FLOAT_CONTRACT` in primitive hashes; pretty-printing `Float` records as literals; DESIGN.md §13 lists the new trusted rules |
| `driver` | `build.rs`: rustc version and target in `FINGERPRINT` |
| `elab` | `Kind::Float` in `numbers.rs` (the new decimal-literal step, the minus default moved after pass 1, whole literals, refusals, negative literals at `Float`; §2.4); `std/Float/Float.sw` (type, `isValid`, `Bool.canonicalTrue`, `Float.make`, `bitsExt`, `neg`/`abs`/`isNaN`/`isFinite`, `ieeeEq`/`ieeeLt`/`ieeeLe`, `toInt`, primitives' signatures, `DecEq`, `Ord`, `Show` with `toSource`, conversions) and their proofs |
| `rt` | `Value::Float(f64)` with the canonicalising constructor; `FloatNative` table bound by hash; lowering of the record, `.bits`, the constructor; `ryu-js` for `toText`; JS `Math.round` rule |
| `js` | `Boundary::Float` (`number`, all values), codec, `.d.ts`; operators and `Math.*` calls; `Object.is` for `DecEq`, `===` for `ieeeEq`; literals from bits; the canonical-bits module (`toCanonicalBits`/`fromCanonicalBits`, §3.5) behind `.bits`, the dynamic constructor, the order key and hashing |
| docs | `docs/syntax.md` (literals, `Float` operators, `ieeeEq` and porting `===`), `docs/core.md`, DESIGN.md §12–13 |

### 7.2 Stages and cost

| Stage | Contents | Code size (guess) |
|---|---|---|
| 1a | **The thin end-to-end slice**, below | 800–1200 lines with tests |
| 1b | the rest of D687's operations (`mul`, `div`, `rem`, `floor`, `ceil`, `trunc`, `round`, `ofInt`/`ofNat`, `isFinite`), `Ord Float`, `ieeeLt`/`ieeeLe`, `toInt` and the safe conversions, `toText`/`toSource`, the full §7.4 table | 900–1300 lines |
| later | `sqrt`, `min`/`max`, `Float.ofText`, `FiniteFloat`, an operations record in std, the general `toInt`/`ofInt` theorem (needs an `ofInt` model) | small each, when needed |
| later | full model (§6.3) | large; its own design note |

**Stage 1a, in order.** Each step's tests pass before the next starts.

1. **Gate: definitional agreement in the kernel** (§3.4). `std/Float/Float.sw` with the type,
   `isValid`, `Bool.canonicalTrue`, `Float.make`, `Float.nan`, `isNaN`, `neg`, `abs`, `bitsExt`,
   `DecEq Float` (via `bitsExt`) and `ieeeEq`; the bodyless primitives `add` and `sub` with the
   kernel reduction rule (always on), their admission, operation tags and `FLOAT_CONTRACT`; the
   ordinary natives for `neg`, `abs`, `isNaN` and `DecEq Float`'s decision; just enough
   elaboration to write the checks (decimal literals elaborated to `{ bits = k, valid = Eq.refl
   True }`, `Kind::Float` with the new defaulting order, negative literals as `Float.neg`). Exit:
   every row of §3.4's acceptance table, natives on and off, native and WASM kernels; `neg (neg
   x) = x` proved. If a row fails, the definitions' shape (D731) is revisited before anything
   else is built.
2. **The rest of the front end:** the lexer's `Tok::Float` and the `xs.0.1` rule; the literal
   refusals (§2.3's table); the §2.4 defaulting table as elaboration tests; the existing
   numeric-group and negative-literal elaboration tests still pass (the moved minus default).
3. **Run time:** `Value::Float` in the Rust runtime with the canonicalising constructor; the
   generated JS with the canonical-bits module (§3.5); the record constructor and `.bits` in both;
   natives bound by hash.
4. **Boundary:** `Boundary::Float`, codec and `.d.ts` (D685).
5. **Plumbing and paths:** rustc and target in `FINGERPRINT`; the four-path differential test
   (native kernel, WASM kernel, Rust runtime, Node) for `add`, `sub`, `neg`, `abs`, `DecEq`,
   `ieeeEq`, the constructor and `.bits`, compared by canonical bits; the contract-plumbing rows
   of §7.4.

Out of 1a: everything listed for 1b; `toText` (so 1a programs can't print floats yet, only their
bits, which is enough for its tests).

The line counts are code-size guesses. **The main uncertainty is not code size** but (1) how hard
the proofs over the bits are (the `valid` obligations of `neg` and friends, `Ord.byKey`'s
injectivity for the total-order key), which may need `Nat` bit lemmas that don't exist yet; (2)
whether the exact definitions can be written so that their natives agree with them definitionally
(§3.4), which step 1 settles first; and (3) getting the trusted computation to agree across the
four execution paths, which 1a is designed to expose early. The `toInt`/`ofInt` inverse theorem is
not on this list: it needs a model of `ofInt`, not bit lemmas, and is deferred (§6.1).

### 7.3 Risks

- **Trusted base grows** by ~11 reduction rules and the NaN canonicalisation (`toInt` is no longer
  one; `toText` doesn't reduce in the kernel). Mitigated by the contract (§3.3), the differential
  tests and listing them in DESIGN.md §13.
- **NaN bits** differ by platform and in WASM; D701 makes the Rust runtime canonical by
  construction and keeps all of JS's bit reinterpretation in one audited module.
- **Natives that disagree with their definitions on proof fields** would make `rfl` proofs depend
  on the natives mode. D731's single constructor and the §3.4 checks, as stage 1a's first gate,
  address it; a native that can't be made to agree stays out of the kernel.
- **Porting `===` and `<` is manual** (D683): a port that writes `==` for `===` compiles and
  differs on `-0` and NaN. Mitigated by §6.4's audit, and docs.
- **A new kernel mechanism** (bodyless primitives that compute). Small, but it is kernel code.
- **Hash binding**: editing `std/Float` needs the natives re-checked; the existing test pattern
  catches it.

### 7.4 Acceptance tests

From draft 1, kept:

1. **Canonical bits** for each operation on random doubles plus an edge set: ±0, NaN, ±∞, the
   smallest subnormal, `MAX_VALUE`, 2^53 ± 1, halves (`±0.5`, `±2.5`), `0.49999999999999994`,
   `4503599627370497`. JS results come from Node in the test. Results are compared as
   `toCanonicalBits(a) = toCanonicalBits(b)` in hex (§3.5): only NaNs are canonicalised, every
   other pattern must match exactly, `-0` vs `0` included. The same canonicalisation is applied to
   any TypeScript oracle's results.
2. **Literals:** 10,000 random decimal strings (plus hard cases such as
   `2.2250738585072011e-308`): elaborated bits = Node's `Number(text)` bits; the §2.3 table
   (`0.0`, `-0.0`, `0e-400`, `0e400`, `5e-324` and `9007199254740994` accepted; `±1e-400`,
   `±1e400`, `9007199254740993` refused).

   **Defaulting** (§2.4's table): `-1 + 0.5`, `0.5 + -1` → `Float`; `def x: Float := -0` (bits
   `0x8000000000000000`); with `t: Float`: `t + -1`, `-1 + t`, `-1 * t`, `-t` → `Float`; with
   `i: Int` also: `t + i` and `t + (-i)` → type error; `-0` otherwise unconstrained → `Int`, `0`;
   `-(id 1)` still `Int`.
3. **Printing:** the Rust runtime's `toText` = Node's `String(x)` on the same set (a test of the
   two interpretations we ship, not a cross-runtime promise, §2.6); `toSource` reads back to the
   same bits on both runtimes; `toSource` of NaN, ±∞ and `-0.0` reduces in the kernel.
4. **Boundary:** `-0`, `80281.87`, NaN, ±Infinity round-trip (`Object.is`); a `bigint` and a
   string are refused; `identity (makeInfinity ())` works through the exports; `Option Float` as
   `undefined`.
5. **Operators:** `0.0 == -0.0` is `False`, `Float.nan == Float.nan` is `True`,
   `Float.ieeeEq 0.0 (-0.0)` is `True`, `Float.ieeeEq Float.nan Float.nan` is `False`; `-0.0 < 0.0`
   holds; `Math.round` cases of §2.5; `rfl : 0.1 + 0.2 = 0.30000000000000004`; `x + 0.0` is not
   simplified.
6. **End to end:** `examples/extract/float-times.sw`, an exported function over times like
   `80281.87`, called from a TS test, matching the same function written in TS, compared by
   canonical bits.
7. **Rejections:** `t + n` with `n: Int`; `9007199254740993`, `±1e400`, `±1e-400` as `Float`;
   `pow` absent; `xs.0.1`.
8. **Definitional agreement** (round 2): every row of §3.4's acceptance table, natives on and off,
   compared as whole terms. Stage 1a's first gate.

Added from the first review:

| Area | Requirement |
|---|---|
| Execution paths | Compare the native kernel, the WASM kernel, the native runtime and generated JS explicitly, for every operation |
| NaN abstraction | Several NaN signs and payloads (made with typed arrays in JS, `from_bits` in Rust) through `.bits`, `DecEq`, `Ord`, and hashing: all give the canonical result |
| Canonical-bits module (round 2) | `toCanonicalBits(fromCanonicalBits(b)) === b` for valid canonical `b`, and `Object.is(fromCanonicalBits(toCanonicalBits(x)), x)` for every `x`, on the edge set, random patterns and NaN payloads; the dynamic constructor `{ bits = b, … }` with run-time `b` gives the encoded double; no typed array or `DataView` outside the module |
| Binary operations | All pairs from the edge set, including signed zeros, subnormals, infinities and extreme magnitudes |
| Representation lowering | Constructor and `.bits` through generic functions and derived `DecEq` on records with `Float` fields |
| Operator resolution | After inlining and specialisation, `==` and `Float.ieeeEq` (and `<` vs `ieeeLt`) stay distinct (§4.4) |
| Conversions | `toInt` on large whole doubles (`1e100`, `MAX_VALUE`), huge positive and negative integers through `ofInt`, halfway cases, the overflow thresholds |
| Optimisation | Folded vs run-time results agree; no reassociation, no FMA contraction (an `a * b + c` case whose fused result differs) |
| Port behaviour | Signed-zero equality branches, duplicate timestamps, sort stability, internally produced non-finite values |
| Test transport | Exchange hex canonical bit patterns (or another lossless encoding of them), never JSON numbers, including in the app's own differential test |
| Contract plumbing | Two float primitives of the same type hash differently; bumping `FLOAT_CONTRACT` changes their hashes; the fingerprint changes with the rustc version |

## 8. Decisions

All decisions are final. D680–D689 were approved by the first review (D696), which flipped D683 and
D685; D701 and D702 came from it; the second review approved all of them with the amendments
listed (D730); D731–D733 are this draft's. Each entry gives the final answer, then the alternatives
set aside.

1. **D680 Name.** `Float`, in `std/Float`. *Decided.*
2. **D681 Model in the logic.** (c): a record of the canonical bits; exact operations defined over
   the bits (`neg` with an explicit NaN case, `toInt` a definition, not a primitive); rounding
   operations bodyless primitives. Set aside: (a) fully opaque; (b) full model now. *Decided per
   both reviews.*
3. **D682 Check-time computation.** The checker computes primitives on known doubles under the
   trust contract of §3.3 (the commuting equation with α extended to every type, conditions C1–C6,
   reduction on values, operation tags and `FLOAT_CONTRACT` in hashes, rustc and target in the
   fingerprint), always on; the reducer returns `{ bits = k, valid = Eq.refl True }`, the same
   record as the literal elaborator. Set aside: primitives never reduce. *Decided per both
   reviews.*
4. **D683 Operators on `Float`.** *Flipped in draft 2.* `== != < <=` keep their lawful meanings
   (`DecEq`, `Ord Float`); JS's `===`, `<`, `<=` are `Float.ieeeEq`, `Float.ieeeLt`,
   `Float.ieeeLe` in ported code, with `>`/`>=` reversed after evaluating the operands left to
   right (§6.4); compilation keeps them distinct. Set aside: draft 1's IEEE operators on `Float`.
   *Decided per both reviews.*
5. **D684 `Ord Float`.** IEEE `totalOrder`, one NaN greatest, used by `<`, sorting, maps and
   deriving; ports keep their comparator and stability (§6.4); native JS `Map`/`Set` lowering
   would need canonical-bit keys. Set aside: no `Ord Float`. *Decided per both reviews.*
6. **D685 Boundary.** *Flipped in draft 2.* `number`; decoding accepts every `number`, NaN and
   ±Infinity included, every NaN denoting `Float.nan` under α (the JS value itself is passed
   through); encoding passes the value. Set aside: draft 1's refusal of NaN and ±Infinity. *Decided
   per both reviews.*
7. **D686 Literals.** `1.5`, `1e3`, `1.5e-7`; correctly rounded; elaborated to bits once, hashed
   as bits, JS generated from the bits; `-k` at `Float` is `Float.neg`, so `-0` is `-0.0`; whole
   literals exact or refused; no `Float` token right after `.`; a literal is refused when it
   overflows (rounds to ±∞) or when its mathematical value is nonzero but rounds to zero (`0e-400`
   is accepted, `1e-400` refused). Set aside: no exponent form; accepting overflow and underflow
   as JS does. *Decided per both reviews.* (The defaulting order is D732.)
8. **D687 Stage-1 operations.** `+ - * / %` (no divisor proof), `neg`, `abs`, `floor`, `ceil`,
   `trunc`, `round` (the full JS rule), `isNaN`, `isFinite`, `ieeeEq`/`ieeeLt`/`ieeeLe`, the
   conversions of §2.5 with `toInt` as a definition over the full range; no `pow` or
   transcendental functions. Proofs about conversions: the exact decoder and concrete
   computations; the general `toInt`/`ofInt` inverse (which must exclude `-0.0`) is deferred until
   `ofInt` has a model (§6.1). Set aside: `sqrt`, `min`, `max` now. *Decided per both reviews.*
9. **D688 Printing.** `toText` is opaque: a bodyless primitive with no kernel reduction rule and a
   backend-supplied, pure, deterministic interpretation respecting α (JS `String(x)`; `ryu-js` in
   the Rust runtime); no promise of identical strings across runtimes in stage 1; kernel
   computations that consume its result are stuck; it is total at run time but not
   kernel-executable. Set aside: specify and test supported engines' `Number::toString` and let
   the kernel reduce it; one Stitchwort formatter on every backend. *Decided per both reviews.*
   (`toSource` is D733.)
10. **D689 Operations record for proofs.** `TimeOps` stays in the ported module, laws as a separate
    hypothesis; the `TimeLaws` comment names `ieeeTimeOps`. Set aside: a generic record in std
    now. *Decided per both reviews.*
11. **D701 Run-time representation invariant.** Physically canonical in the kernel and the Rust
    runtime (one canonicalising constructor); in JS, NaN-agnostic values, with all Float bit
    reinterpretation in one audited module, `toCanonicalBits`/`fromCanonicalBits`, with the two
    laws of §3.5: `.bits`, the dynamic constructor, the order key and hashing go through it, and
    typed arrays and `DataView` appear nowhere else. Differential tests compare canonicalised bits
    (only NaNs canonicalised), the TS oracle's included. Set aside: arbitrary NaNs everywhere with
    every representation-sensitive operation audited; canonicalising every JS result. *Decided per
    both reviews.*
12. **D702 Finiteness.** No `FiniteFloat` in stage 1: the port checks finiteness on its own
    decoding or validation path, since an erased proof field checks nothing at run time;
    `FiniteFloat`, a checked `number` like `SafeNat`, joins std when a program wants the check at
    the boundary. Set aside: `FiniteFloat` in stage 1. *Decided per both reviews.*
13. **D731 Native/definition agreement (new).** Every exact definition returning a `Float` builds
    it with `Float.make`, whose witness `Bool.canonicalTrue (Float.isValid n) p` reduces to
    `Eq.refl True` on known valid bits whatever `p` is; `Float` natives fire only on known bits and
    return that record; proof-carrying natives return the definition's proof term, or are
    restricted or left out of the kernel. Propositional equality of equal-bit records is
    `Float.bitsExt`, by `Bool.uniqueEq`. §3.4's checks, natives on and off, are stage 1a's first
    gate. Set aside: natives that reproduce each definition's own proof structure (more trusted
    code per native); omitting all `Float` kernel natives (slower checking for no gain if the gate
    passes). *Decided: an implementation choice among the review's options.*
14. **D732 Defaulting order (new).** Expected type, then decimal/exponent literals, then typed
    operands (pass 1), then the unary-minus default to `Int` for an otherwise undecided group,
    then pass 2 and today's defaults (§2.4). Leaves with literals inside are not consulted before
    the minus default, so `-(id 1)` stays an `Int`. Set aside: the minus default after pass 2
    (would make `-(id 1)` a negative-`Nat` error). *Decided per the second review.*
15. **D733 `toSource` (new).** `toSource` is a field of `Show`, so a language-level function, not
    compiler tooling: `Float.toSource` is an ordinary definition (NaN, ±∞ and `-0.0` decided from
    the bits; otherwise `toText` with `.0` appended when it has no `.` or `e`), whose output reads
    back as the same `Float` on every backend. Set aside: a second opaque primitive with its own
    contract. *Decided: the review asked for it to be specified if it is a language function.*

## Appendix A: snippets run

Node 22.23.3 and rustc 1.99.0 on macOS/arm64; the scripts are `float-checks.js` and
`float_checks.rs` in the session scratchpad. Output, abridged:

```
round 0.49999999999999994 -> Math.round 0  floor(x+0.5) 1
round -0.5 -> Math.round -0  floor(x+0.5) 0
round -0 -> Math.round -0  floor(x+0.5) 0
round 4503599627370497 -> Math.round 4503599627370497  floor(x+0.5) 4503599627370498
round -2.5 -> Math.round -2  floor(x+0.5) -2
BigInt(1e100) === 10n**100n false 10000000000000000159028911097599180468360808563945281389781327557747838772170381060813469985856815104
JSON.parse("1e400") Infinity MAX+MAX Infinity
1e400 literal Infinity 1e-400 0 -1e-400 -0
9007199254740993 -> 9007199254740992 9007199254740994 -> 9007199254740994
stable sort a,b
Map size after 0 and -0 1 Set size of [0,-0,NaN,NaN] 2
-0 === 0 true Object.is(-0,0) false NaN===NaN false
String 1e+21 1e-7 0 0.30000000000000004 5e-324
bits NaN 7ff8000000000000 bits 0/0 7ff8000000000000
negative payload NaN read back fff8000000000001 Object.is(nf, NaN) true after nf*1 fff8000000000001
-1 + 0.5 -0.5 0.5 + -1 -0.5
0.0 + -0.0 0

(Rust)
total_cmp(-NaN, -inf) = Less
total_cmp(+NaN, +inf) = Greater
total_cmp(-0, +0) = Less
-(canonical NaN) bits = fff8000000000000
round(-2.5) = -3, round(-0.5) = -1, round(0.49999999999999994) = 0
parse 1e400 = Ok(inf)
parse 1e-400 = Ok(0.0), -1e-400 sign negative = true
parse 9007199254740993 = 9007199254740992
parse 80281.87 bits = 4680253341308362424
0/0 bits (black_box) = 7ff8000000000000
```

## Sources

- Lean reference, Floating-Point Numbers: https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/
- Rocq reference, primitive objects: https://rocq-prover.org/doc/master/refman/language/core/primitive.html
- Rocq `PrimFloat` (IEEE `eqb`, `Leibniz.eqb`): https://docs.rocq-prover.org/v8.20/stdlib/Coq.Floats.PrimFloat.html ; `FloatOps` (`Prim2SF`): https://rocq-prover.org/doc/v9.0/corelib/Corelib.Floats.FloatOps.html
- Isabelle AFP, IEEE_Floating_Point: https://isa-afp.org/entries/IEEE_Floating_Point.html
- F\* `FStar.Float64.fsti`: https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Float64.fsti
- Dafny releases: https://github.com/dafny-lang/dafny/releases
- Liquid Haskell's encoding of `Double` as reals (secondary): https://arxiv.org/pdf/2508.14249
- Agda built-ins, Floats: https://agda.readthedocs.io/en/latest/language/built-ins.html
- Idris 2 `Decidable.Equality`: https://github.com/idris-lang/Idris2/blob/main/libs/base/Decidable/Equality.idr
- ReScript primitive types: https://rescript-lang.org/docs/manual/primitive-types
- PureScript `Prim`: https://pursuit.purescript.org/builtins/docs/Prim
- Elm `Basics`: https://github.com/elm/core/blob/master/src/Basics.elm
- Rust `f64`: https://doc.rust-lang.org/std/primitive.f64.html
- MDN `Math.round`: https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Math/round
- WebAssembly nondeterminism: https://www.webassembly.org/docs/nondeterminism/
- `ryu-js`: https://docs.rs/ryu-js
- ECMAScript (cited by the review: Number::toString, RoundMVResult, `Math.round`, `Math.sqrt`, `Array.prototype.sort` stability, SameValueZero, JSON number parsing, BigInt/Number conversions): https://tc39.es/ecma262/
