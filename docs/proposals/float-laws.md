# Proposal: laws about `Float`'s rounding operations

**Status:** proposed, 26 October 2026. A research and design note; nothing here changes the
compiler. Written against commit `50214b95`. Decisions D1363–D1366 are [at the end](#9-decisions),
each with a recommended option, for Matt to decide.

Labels: **[checked]** (read in this repository, `file:line`), **[inferred]** (my reasoning, not
stated anywhere or not tested), **[ran]** (run while writing this: Node 22.23.3 on macOS/arm64; the
scripts are in [Appendix A](#appendix-a-scripts-run)), **[read]** (read in the linked source; quoted
verbatim where the wording matters). Papers marked **read in full** were read end to end, not just
their abstracts.

## 0. Summary

**The question.** `Float` is an IEEE 754 double. Its exact operations (order, `==`, `neg`, `abs`,
`isFinite` …) are ordinary definitions over its 64 bits, so laws about them can be proved. Its
rounding operations (`add`, `sub`, `mul`, `div`, `rem`, `floor`, `ceil`, `trunc`, `round`, `ofInt`,
`ofNat`) are *primitives*: the checker computes them on known values with Rust's `f64`, but in a
proof about unknown values they are unknown functions with no laws. Should std be able to prove
laws about them, and how?

**The trigger.** A proof about a real-world app's merge logic needs "adding a non-negative number
never gives a smaller result", `0.0 <= d → s <= s + d`, in `Float`'s total order (where `-0.0 <
0.0` and the NaN is the single greatest value). Today the proof carries this as a hypothesis that
no caller can discharge.

**Is the law true?** Yes, in every case: zeros, infinities, the NaN, subnormals and overflow
([§3](#3-the-trigger-law-case-by-case)). Five million random and edge-case pairs agree [ran]. But
three nearby "obvious" laws are false: `x + 0.0 = x` (fails for `-0.0`), `0.0 <= d → s - d <= s`
(fails for `d` the NaN) and `x <= y → x + z <= y + z` (fails for `-∞ <= 0.0` with `z = +∞`) [ran].
A wrong law, once trusted, proves anything.

**What others do.** Rocq: a full specification model in the logic plus one *axiom* per primitive
saying the primitive equals the model; two of those axioms have been wrong, each giving a proof of
`False` ([§4.1](#41-rocq-primitive-floats)). Lean (since June 2026), Isabelle and HOL4: the
operation *is* a definition over bits, with no axiom, and compiled code uses the hardware instead
([§4](#4-how-other-systems-do-it)).

**Recommendation: option (d), no axioms.** Give each rounding operation a real Stitchwort
definition over the bits, and keep the `f64` computation as a *native* for it, exactly as `Nat.add`
is a definition with a native today. Then:

- nothing new is assumed: the trusted reduction rules become natives that are tested against
  their own definitions, inside the kernel, by the gate that already runs with float natives off;
- checking speed on known values doesn't change, because the native still fires;
- any true law can be proved, and std proves the few that programs need, starting with the
  trigger's.

The model should be the simple "exact, then round" one: every finite double is a whole number of
units of 2^-1074, so `x + y` is "add the two whole numbers exactly, then round to the nearest
double". One rounding function then serves `add`, `sub`, `mul`, `ofInt` and `ofNat`, and monotonicity
laws come from two small facts about it ([§7](#7-recommendation)). Four stages; the trigger law is
proved at the end of the second ([§8](#8-staging)).

## 1. Terms, plainly

- **Rounding.** The true sum of two doubles is usually not a double. IEEE 754 says the result is
  the double *nearest* the true sum; on a tie, the one whose last bit is 0 ("ties to even").
- **Correctly rounded.** An operation computed "as if with infinite precision, then rounded once".
  IEEE requires this for `+ - * /` and square root.
- **Subnormal.** The tiny doubles near zero with fewer significant bits. Some hardware modes
  replace them by zero ("flush to zero"), which IEEE does not allow by default.
- **Total order.** Stitchwort's `<=` on `Float`: `-∞ < … < -0.0 < 0.0 < … < +∞ < NaN`, one NaN
  ([checked] `crates/elab/src/std/Float/Float.sw:247-253`, `:275-279`).
- **Axiom.** A statement the logic accepts without proof. If it is false, the logic proves
  everything, `False` included.
- **Trusted reduction rule.** A rule by which the checker *computes* (`0.1 + 0.2` becomes
  `0.30000000000000004`) whose correctness the checker can't check. A wrong rule also makes
  `False` provable (one computation by the rule, another by a definition), so it is trust of the
  same kind as an axiom, but only about known values.
- **Native.** In Stitchwort, a fast Rust implementation of an *ordinary definition*. It must give
  exactly what the definition gives; tests compare them, and switching natives off makes the
  definition run instead.

## 2. What Stitchwort does today

**The type.** `type Float = { bits: Nat, valid: Float.isValid bits = True }`, with the NaN
canonical ([checked] `Float.sw:30-34`). Results are built by `Float.make`, whose witness reduces to
`Eq.refl True` on known bits (`Float.sw:40-46`).

**The rounding operations are bodyless primitives.** "The rounding operations: primitives, with no
definition. The kernel computes them on known doubles (rounding to nearest, ties to even, the NaN
canonical), and the runtime and JS use the machine's" ([checked] `Float.sw:205-208`; the
declarations are `Float.sw:208-236`). In the kernel, `crates/core/src/float.rs:769-830` forces the
arguments, and if their bits are known computes `FloatOp::apply` (`a + b` etc. on `f64`,
`float.rs:264-273`) and makes a NaN canonical (`float.rs:133`); otherwise the call is stuck
[checked]. This rule "is part of evaluation, always on: it isn't a native, so switching the natives
off doesn't change it (a primitive has no definition to fall back to)" ([checked]
`float.rs:20-24`).

**The trust position, as written.** "No new propositional axioms (equality and order are proved,
not assumed), but new trusted reduction rules. … Replacing a primitive with a checked definition
later (§6.3) would improve assurance even if every result stayed the same" ([checked]
`docs/proposals/float.md:712-715`; the wording came from review, `float.md:292`). DESIGN.md's
soundness table repeats it ([checked] `DESIGN.md:953`). Stitchwort's only axiom today is
`Quot.sound`, and `stitchwort axioms` lists axioms a definition depends on ([checked]
`DESIGN.md:949`, `docs/core.md:433`); there is no `assume` yet ([checked] `docs/core.md:15`).

**What can be proved, and what can't.** §6.1 of the float note: structural facts, facts about the
exact definitions, and facts about known doubles by `rfl`; but "stage 1 provides no practical
general reasoning framework for rounded arithmetic" ([checked] `float.md:1134-1161`). §6.3 already
names the way out: "Giving `add` and the rest definitions over the bits (Lean's route), or the
integer × 2^exponent view with exact-then-round (Flocq's), would make rounding-error theorems
possible and turn the primitives into ordinary natives" ([checked] `float.md:1199-1206`). The
language table says "Nobody proves algebraic laws about doubles in everyday code" (`float.md:385`);
the trigger is a counterexample to that, and the table's Lean row (`float.md:365`) is now out of
date in one respect ([§4.2](#42-lean-4)).

**How `Nat` and `Int` are done, for comparison.** `Nat` is defined as `Zero | Succ Nat`, and
`Nat.add` etc. are ordinary definitions ([checked] `crates/elab/src/std/core/Data.sw:9-22`). "A
few prelude definitions also have a native implementation, used when all their arguments are
numbers. Otherwise they unfold as usual, so proofs by induction still work. The native
implementations are part of the trusted base … Each must compute exactly what its definition
computes" ([checked] `crates/core/src/native.rs:9-17`). `Int` has no kernel natives at all: its
operations are definitions over `Nat`'s ([checked] `DESIGN.md:951`; decision K1,
`docs/proposals/integers.md:532-536`). So `Nat` is already option (d) below: a definition, with
the machine as a trusted, tested acceleration of it. The float exact operations (`neg`, `abs`,
`isNaN`, `toInt` …) work the same way, with natives bound by content hash ([checked]
`float.rs:25-35`).

**The gate already compares definitions with natives.** Stage 1a's gate runs every check with the
float natives off and the number natives on, comparing whole normal forms, proofs included
([checked] `float.md:193-209`; `Builtins::disable_float_natives`, `crates/core/src/native.rs:152`,
`:182`).

**Runtimes.** The Rust runtime computes every float primitive with the same `FloatOp::apply`
([checked] `crates/rt/src/prims.rs:383-393`). The native (Cranelift) backend has inline fast paths
only for `Nat` `add`/`sub`/`mul`/`divFuel` and calls the runtime's `prim` helper for every other
primitive ([checked] `crates/native/src/n1.rs:3803-3866`), so floats there are also Rust `f64`
[inferred from that code; no float instruction is emitted in `n1.rs`]. JS uses the engine's
`number` operators. `crates/cli/tests/float_paths.rs` compares the native kernel, the WebAssembly
kernel, the Rust runtime and Node on every operation over an edge set and random patterns
([checked] `float_paths.rs:1-20`, `float.md:113-126`).

## 3. The trigger law, case by case

**Claim.** For all `s` and `d` of type `Float`: if `0.0 <= d` in the total order, then
`s <= s + d` in the total order.

`0.0 <= d` means `d` is `+0.0`, a positive finite double (normal or subnormal), `+∞`, or the NaN;
it excludes `-0.0` and every negative.

The facts used, from IEEE 754 as JavaScript states it: `Number::add` returns NaN if either operand
is NaN, NaN for `+∞ + -∞`, the infinite operand if one is infinite, `-0` only for `-0 + -0`, and
otherwise "𝔽(ℝ(x) + ℝ(y))", the double nearest the exact sum, ties to even, where "if +0𝔽 was
chosen, replace it with -0𝔽 if and only if x < 0" and a value of 2^1024 or more becomes `+∞` [read,
ECMAScript §6.1.6.1 and §6.1.6.1.7]. Rounding to nearest is *monotone*: `x ≤ y` (real numbers)
implies `round(x) ≤ round(y)`, and it leaves a double unchanged [read: the ITP 2019 paper,
§2.2.1.2, defines a rounding as "an increasing function … whose restriction to F is identity"].

| `s` | `d` | `s + d` | `s <= s + d`? |
|---|---|---|---|
| any | NaN | NaN | yes: the NaN is greatest |
| NaN | any | NaN | yes: NaN <= NaN |
| `-∞` | `+∞` | NaN | yes: the NaN is greatest |
| `-∞` | `+0.0` or finite | `-∞` | yes: equal |
| `+∞` | `+0.0`, finite, `+∞` | `+∞` | yes: equal |
| finite or zero, not `-0.0` | `+0.0` | `s` (exact) | yes: equal |
| `-0.0` | `+0.0` | `+0.0` (opposite-signed zeros give `+0`) | yes: `-0.0 < 0.0` |
| finite or zero | `+∞` | `+∞` | yes |
| finite or zero | positive finite | the double nearest the real `s + d` | yes, below |

The last row: the real sum `s + d` is strictly greater than the real `s`, so by monotonicity
`round(s + d) ≥ round(s) = s` as real numbers. To move from "≥ as reals" to "<= in the total order"
three things need checking:

- **A zero result.** If `round(s + d)` is a zero, it is `+0.0` unless the real sum is negative;
  but the sum is never a nonzero number that rounds to zero, because with subnormals the exact sum
  of two doubles is a multiple of the smallest subnormal, so it rounds to zero only if it *is* zero
  [read: Flocq's Theorem 9, `round_plus_eq_zero`, "round(x + y) = 0 ⇒ x + y = 0" for formats
  without flush-to-zero]. A zero sum means `s = -d < 0`, and `+0.0` is above every negative.
- **Equal values.** If `round(s + d)` equals `s` as a real and `s` is not zero, both are the same
  double, so the same bits. `s` can't be zero here, since then the sum is `d`, which is positive.
- **Overflow.** A sum of 2^1024 or more (after rounding) becomes `+∞`, which is `>=` every finite
  `s` [read, ECMAScript].

So the law holds with no exceptions. **[ran]**: 4,999,773 pairs with `0.0 <= d` (every pair of a
29-value edge set, and random bit patterns with random, tiny and proportional `d`), no failure.

**What the law depends on.** Round-to-nearest (or any monotone rounding), subnormals kept, and the
canonical NaN being the greatest. It would *fail* under flush-to-zero: with `s = 5e-324` (the
smallest subnormal) and `d = 0.0`, the exact sum is `s`, which flush-to-zero turns into `0.0`, below
`s` [inferred from the definition of flush-to-zero; not run, since no supported runtime does it].
Condition C2 forbids flush-to-zero ([checked] `float.md:752`), so this is one more thing that
condition protects.

**Nearby laws that are false** [ran, `laws.js`]:

| Law | Status | Counterexample |
|---|---|---|
| `x + 0.0 = x` | false | `-0.0 + 0.0` is `0.0` |
| `x + (-0.0) = x` | true (no counterexample; follows from the add rules above) | |
| `x + y = y + x`, `x * y = y * x` | true with the canonical NaN | |
| `x - y = x + (-y)` | true (it is how ECMAScript defines `Number::subtract`) | |
| `-(x + y) = (-x) + (-y)` | false | `x = 0.0`, `y = -0.0` |
| `0.0 <= d → s - d <= s` | false | `d` the NaN: `s - NaN` is the NaN, the greatest |
| `x <= y → x + z <= y + z` | false | `-∞ <= 0.0`, `z = +∞`: NaN vs `+∞` |

The last two fail only because the total order puts the NaN on top. This is why laws need proofs
(or at least tests that hit every edge pair), not intuition.

## 4. How other systems do it

### 4.1 Rocq: primitive floats

Bertholon, Martin-Dorel and Roux, "Primitive Floats in Coq", ITP 2019 [**read in full**]. Coq gets a
primitive type `float`, implemented by the machine's binary64 operators in all three reduction
engines (§3.1, §3.3). It is useless for proofs on its own: "Although floating-point computations
are possible, they remain entirely useless in proofs at this point, since there is no specification
of their behavior" (§3.2). So:

- **A specification model.** `spec_float` (zero, infinity, NaN, or sign/mantissa/exponent with no
  bounds) and functions like `SFmul`, "mostly borrowed from the IEEE754.Binary module of the Flocq
  library and totals 398 lines" (§3.2). `SFmul` multiplies mantissas exactly and rounds with a
  round bit and a sticky bit.
- **Axioms tying the primitives to it.** `Prim2SF : float -> spec_float` and its inverse, three
  axioms making them a bijection with the valid specification floats, and then "all of the fifteen
  operators … are linked to their specification by an axiom such as … `Axiom mul_spec : forall x
  y, Prim2SF (x * y)%float = SFmul (Prim2SF x) (Prim2SF y)`" (§3.2). The current file has the same
  shape: `add_spec`, `sub_spec`, `div_spec`, `leb_spec` and the rest [read,
  `theories/Corelib/Floats/FloatAxioms.v`, lines 27-83].
- **`Print Assumptions`.** "such an error in the specification can only be harmful when the
  corresponding axiom is used. It is worth noting that all the axioms used in a proved theorem
  explicitly appear in the result of the Coq command Print Assumptions" (§4.3). The reference
  manual: "These primitive declarations are regular axioms. As such, they must be trusted, and are
  listed by the `Print Assumptions` command" [read, Rocq reference manual, primitive objects].
- **Laws.** Through a link to Flocq, "giving access to all the results already proved in the
  library" (§3.2).
- **Soundness threats named by the paper** (§4.3): specification mismatches; different results in
  different engines or machines (hence all NaNs are equal in the logic); "Double roundings due to
  the x87 on old 32 bits architectures could also be harmful. The OCaml compiler systematically
  relies on it, forcing us to implement all floating-point operators in C and to use the
  appropriate compiler flags. A runtime test is eventually added to prevent Coq from running in
  case of miscompilation"; and an incorrect convertibility test (IEEE equality would equate `-0`
  and `+0`).
- **What came before.** Coq's first machine integers used "the so-called retro-knowledge approach,
  which consisted in developing a reference implementation of 31-bit integer operators in Coq …
  then optimizing their evaluation … by replacing the considered Coq operator on-the-fly with the
  corresponding hardware operator. The implicit assumption here is that both implementations
  match" (§2.1). That is option (d). It was replaced by primitive integers for "a compact
  representation of integers, and making explicit the axioms that specify the primitive operators".
  Stitchwort already has a compact representation (a `Float` is a record holding a `Nat` literal,
  `float.md:830`), so the first reason doesn't apply to it [inferred].
- **Speed.** Emulated floats were about 20x slower than primitive ones in `vm_compute` for the whole
  tactic, and 150–275x for single operations (Tables 1–2).

**The spec axioms have been wrong, twice, each a proof of `False`** [read, GitHub issues]:

- rocq-prover/rocq#12483 (Coq 8.11, "priority: blocker, kind: inconsistency"): "Incorrect
  specification of PrimFloat.leb". `SFleb` matched on `Some Le`, but "Since `Le` is not a
  constructor, it becomes an unused variable", so the axiom `leb_spec` said `1 <= 0` is `true`.
- rocq-prover/rocq#16096 (fixed in 8.15.2): "Inconsistent classification of zeros", proved `False`
  by `now generalize (classify_spec 0)`.
- A third, rocq-prover/rocq#17871, was in the native compiler, not the spec: "native_compute +
  evars or binders + primitive floats gives a proof of False".

Each spec bug was a model function that disagreed with the hardware on some input, turned into a
contradiction by the axiom that says they agree. Under option (d) the same model bug would make the
definition compute a different answer from the native, which the natives-off gate would show as a
failed comparison on that input, rather than become an axiom [inferred].

### 4.2 Lean 4

`Float` used to be opaque. Since June 2026 it isn't: PR leanprover/lean4#14079 added `Float.Model`
and #14091, "`Float` is no longer opaque", made `Float` a structure over it and "redefine[d] `add`,
`sub`, `mul`, `div`, `sqrt`, `abs`, `neg`, `isNaN`, `isInf`, `isFinite`, `le`, `lt`, `beq`, `ofInt`,
`ofNat` … to delegate to their `Float.Model` counterparts. This does not change anything about
compiled code; compiled code uses the accelerated functions from the runtime as before" [read, PR
descriptions]. The current source [read, `src/Init/Data/Float/Float.lean`]:

```
@[extern "lean_float_add"] def Float.add : Float → Float → Float :=
  fun a b => .ofModel (a.toModel + b.toModel)
```

`Float.Model` "is defined as the type of `UInt64` with the additional restriction that bit
patterns encoding a `NaN` must be exactly a chosen canonical `NaN`" — the same shape as
Stitchwort's `Float` — and its operations unpack to sign, mantissa and exponent, compute, round and
repack [read, `src/Init/Data/Float/Model/Float.lean`; `Unpacked/Operations/Add.lean` aligns the two
exponents, adds the signed mantissas exactly, then calls `normalize`, which rounds]. No axiom is
involved; the trust is that the C implementation (`@[extern]`) agrees with the definition. "The
logical model is extensively empirically tested against the floating-point operations on all
supported platforms" [read, Lean reference], using "difficult test cases generated using Berkeley
TestFloat and UCBTest" [read, PR #14079].

Lean does **not** provide laws: "It is not a goal of this development to serve as the basis for a
general-purpose floating-point library or to have any direct lemmas written about it at all.
Rather, users … should prove that the operations defined here are equivalent to the operations
defined in the separate library and then transfer lemmas" [read, `Model/Float.lean`]. Mathlib's own
older float type, `Mathlib/Data/FP/Basic.lean` ("Implementation of floating-point numbers
(experimental)"), was deprecated on 2026-10-02 with "no replacement" [read]. A code search of
Mathlib for `Float.Model` found nothing [ran: `gh search code`].

### 4.3 Flocq

Boldo and Melquiond, "Flocq: A Unified Library for Proving Floating-point Algorithms in Coq", ARITH
2011 [**read in full**]. Floats are real numbers `m · β^e`; a format is described by a function `ϕ`
from a number's magnitude to its exponent, and rounding is `Zrnd(scaled mantissa) · β^cexp(x)`
(§III-D, III-E). Laws are theorems: rounding is monotone (Theorem 1 and §III-A's definition of a
rounding predicate as total and monotone), Sterbenz's exact subtraction (Theorem 4), relative error
(Theorem 5), and "when x + y rounds to zero … x + y is mathematically equal to zero" (Theorem 9).
For computation, Flocq locates the exact result between two floats with a "location" (exact, below
half, half, above half), which "are similar to the usage of the round and sticky bits" (§IV-A).

The bit-level part is in Boldo, Jourdan, Leroy and Melquiond, "Verified Compilation of
Floating-Point Computations", J. Automated Reasoning 2015 [read §1–6 in full; skimmed §7 on
integer conversions]. `binary_float` has constructors for signed zero, signed infinity, NaN and
`B754_finite s m e (bounded m e = true)`; operations are executable functions on integers, proved
equal to "round the real result": "the second one offers effective computability, while stating and
proving that the first one is equivalent provides concise specifications" (§5.2), e.g. Theorem 2
(`Bmult_correct`). `binary_float_of_bits` and its inverse are "proved to be inverse of each other"
(§5.3). This replaced CompCert's earlier axioms: "the Float library was not constructed, but only
axiomatized … the algebraic identities exploited during code generation are not proved to be true,
but only asserted as axioms" (§4). So everything in Flocq's `binary_float` is proved without
axioms; Rocq's primitive floats then add axioms only to connect the *hardware* type to it.

CompCert's list of identities that are *false* for doubles is the same lesson as §3: `x ⊕ 0.0 ↛ x`,
`−(−x) ↛ x` (for signalling NaNs) and others, "Viewed as algebraic identities, (4) and (7) do not
hold for x = −0.0" (§6.2).

### 4.4 Isabelle, HOL4, F\*, Why3, Agda

- **Isabelle**: the AFP entry `IEEE_Floating_Point` "provides a formal model of IEEE-754
  floating-point arithmetic … including formal specification of the standard and proofs of
  important properties", added "a model of floating-point arithmetic with a single NaN value" in
  May 2023, and "a code generation setup for floats" [read, AFP entry page]. The `Double` theory
  maps `+ - * /` to SML `Real.+` and OCaml `+.` with the comment "Need to trust a lot of code
  here..." [read, `Double.html`]. That is option (d): definitions in the logic, hardware at run time.
- **HOL4**: `binary_ieeeScript.sml` defines `float = <| Sign : word1; Exponent : 'w word;
  Significand : 't word |>` and its value as a real number — a definitional bit-level model, no
  axioms [read, HOL source].
- **F\***: `FStar.Float64.fsti` declares `val t : Type0` and `val add : t -> t -> t` with no laws
  (option (a)) [read].
- **Why3**: the `ieee_float` theory's type is abstract, "we use the same idea as the SMTLIB floating
  point theory", with axioms such as `add_finite` (`to_real (add m x y) = round m (to_real x +.
  to_real y)` when nothing overflows) and `Round_monotonic` [read, Why3 standard library page].
  Option (c)'s shape, aimed at SMT solvers.
- **Agda**: floats are binary64 in the type checker with "exactly one NaN value"; arithmetic
  primitives come with no laws; `primFloatToWord64Injective` exists, but "primFloatToWord64 cannot
  be guaranteed to be consistent across backends" [read, Agda built-ins]. Option (a).

## 5. Do our runtimes give bit-exact binary64 with round-to-nearest-even?

| Runtime | Specification | Status |
|---|---|---|
| Kernel and Rust runtime (`f64`), native backend (calls the runtime) | Rust RFC 3514: "Primitive operations on floating-point types generally produce results that exactly match IEEE 754-2008", with roundTiesToEven, "without abruptUnderflow/flush-to-zero"; NaN sign and payload non-deterministic; Rust "does not support executing floating-point operations with alternative rounding modes" [read] | Exact on our targets (x86-64, aarch64, wasm32) except NaN bits, which we canonicalise. The RFC's exceptions are i586 without SSE2 ("operations are internally computed with a different precision") and 32-bit ARM NEON, which "always flush-to-zero" [read]; neither is a Stitchwort target [inferred] |
| WebAssembly kernel (the playground) | "Floating-point arithmetic follows the IEEE 754 standard … All operators use round-to-nearest ties-to-even"; a NaN result's "sign is non-deterministic" [read, WebAssembly spec, numerics] | Exact except NaN bits |
| JS | ECMAScript: Number values are "the double-precision floating point IEEE 754-2019 binary64 values … except that the … distinct NaN values … are represented in ECMAScript as a single special NaN value"; `Number::add` "performs addition according to the rules of IEEE 754-2019 binary double-precision arithmetic" with ties to even [read, §6.1.6.1] | Exact by specification; engines are tested, not proved |

**Where trusting hardware floats went wrong before** [read unless marked]:

- **x87 double rounding.** The CompCert paper's opening example gives three different answers for
  the same C program under GCC on x86 depending on flags, because x87 computes with 64-bit
  mantissas and rounds again on store (§1); GCC bug #323 is a miscompilation of the same kind. The
  Coq paper avoids it with C code, compiler flags and a start-up test (§4.3). WebKit dropped x87
  because the 32-bit x86 build "fails a number of stress tests because of one-off rounding errors
  in floating point operations. This is caused by the use of extended precision FP registers"
  [read, WebKit bug 194853].
- **FMA contraction and reassociation.** C lets compilers contract `a*b + c` into one fused
  operation, and `-Ofast` reassociates (CompCert paper §2.2, §2.3). Stitchwort's condition C5
  forbids both (`float.md:755-760`), and the four-path test has a contraction case (`0.1 * 0.1 -
  0.01`, `float.md:115-116`) [checked].
- **Flush-to-zero.** Flocq treats it as a different format (FTZ), where Theorem 9 fails (§IV-B5).
  Stitchwort's C2 forbids it.
- **Wrong specifications in a prover.** The two Rocq issues of §4.1.

None of this changes between the options: every option keeps the runtimes on hardware and keeps
the §3.3 contract. What changes is what the *kernel* trusts.

## 6. The options

### (a) No laws (today)

- **Trusts:** the 11 reduction rules on known values (`DESIGN.md:953`).
- **Size:** nothing.
- **Checking speed:** unchanged.
- **Users can prove:** facts not depending on what rounding computes, and facts about known values
  by `rfl` (`float.md:1134-1161`). The trigger's proof keeps an undischargeable hypothesis, so its
  theorem never applies to a real call.
- **Fit:** matches today's position exactly.

### (b) A small set of trusted laws in std

For example `0.0 <= d → s <= s + d`, `x + y = y + x`, `x - y = x + (-y)`, `x + (-0.0) = x`, each
stated as an axiom, each differentially tested against the hardware like `float_paths.rs`.

- **Trusts:** the reduction rules, plus each law. A wrong law proves `False` for every program, not
  just for known values. Testing can't be exhaustive (2^128 pairs per binary law); Rocq's two
  wrong axioms both shipped in releases before being found ([§4.1](#41-rocq-primitive-floats);
  #12483 was reported against Coq 8.11, #16096 fixed in 8.15.2).
- **Size:** small: a kernel form for named axioms (none exist besides `Quot.sound`,
  `docs/core.md:433`), their report in `stitchwort axioms`, a few laws, a test per law. About a
  stage.
- **Checking speed:** unchanged.
- **Users can prove:** exactly what the list allows. Every new need is a new axiom and a review.
  And plausible laws are often false ([§3](#3-the-trigger-law-case-by-case): three of seven
  candidates).
- **Fit:** breaks "no new propositional axioms" (`float.md:712`), which was the reviewed position.

### (c) Rocq's approach: a model plus one axiom per primitive

Write a reference binary64 in Stitchwort (over bits, or over integers and exponents); add one axiom
per primitive, `Float.add x y = Float.addModel x y`. Laws are then proved from the model.

- **Trusts:** the reduction rules, plus 11 axioms that say the hardware equals the model. A model
  bug becomes `False` (Rocq #12483, #16096).
- **Size:** the model (Rocq's is 398 lines plus Flocq, §3.2; Lean's is about 70 KB of source for
  binary64 and binary32 together [read: file sizes in the Lean tree]); the axioms; proofs of each
  law over the model.
- **Checking speed:** unchanged on known values (the primitive still computes). Unfolding the model
  happens only when a proof rewrites with an axiom and then computes [inferred].
- **Users can prove:** any true law, from the model.
- **Fit:** worse than today on axioms. And in Stitchwort it is strictly dominated by (d): once the
  model exists, the primitive can simply *be* it, so the axiom buys nothing. Rocq needed axioms
  because its `float` is a kernel type with no definition; Stitchwort's `Float` is already an
  ordinary record of bits ([checked] `Float.sw:34`).

### (d) No axioms: the primitives become definitions, the hardware a native

Replace each bodyless primitive by a Stitchwort definition over the bits, and register today's
`f64` computation as that definition's native, as `Nat.add` has one (`native.rs:9-17`). This is
Lean's design since June 2026 and Isabelle's, and Coq's retro-knowledge before primitive integers.

- **Trusts:** the natives agree with their definitions on known valid bits. That is the trust
  `Nat`'s natives already carry, and it is *testable inside the kernel*: switch the float natives
  off and the definition runs, which the gate already does for the exact operations
  (`float.md:193-209`). The reduction rules disappear from DESIGN.md §13; `toText` stays a primitive
  with no rule. Separately, whether the definition matches IEEE is a question of the *meaning* of
  the program, not of consistency: a wrong definition can't prove `False`, it would be a wrong
  `add`, caught by the four-path test comparing it with Node and the hardware [inferred].
- **Size:** largest. A rounding function and the operations (§7); tests of the definitions against
  the hardware on hard cases; proofs of whichever laws std provides. Each operation is a few dozen
  lines; rounding is the hard part, done once. Lean's `Round.lean` is 7.7 KB and `Add.lean` 1.3 KB
  [read: Lean tree sizes].
- **Checking speed:**
  - *Known values, natives on:* unchanged. The native fires on known bits, as now.
  - *Known values, float natives off* (the gate): the definition runs over `Nat` numbers with the
    number natives on. Operations are on integers of up to about 2,100 bits, held as one number
    each; the costly parts are `Nat.pow 2 e`, which recurses `e` times (up to about 2,100;
    [checked] `crates/elab/src/std/Nat/Arith.sw:517-519`), and finding a number's bit length.
    Estimate: thousands of kernel steps per operation, fine for the gate's ~1,100 checks [inferred;
    measure in stage 1].
  - *Unknown values:* a definition stuck on unknown bits stays folded, like the primitive today
    (the unfolding policy, [checked] `docs/core.md:213`). One risk: conversion compares two
    *different* non-recursive definitions stuck on a `case` by their case trees ([checked]
    `docs/core.md:218`), which for big float definitions could be slow when two float terms
    differ. Making them opaque (`opaque def`, [checked] `docs/core.md:162-170`) avoids that, with
    the law files `unfolding` them; whether a native fires on an opaque definition needs checking
    [inferred].
- **Users can prove:** any true law. Std proves the common ones once (§7).
- **Fit:** the reverse of a cost. It completes §6.3's plan (`float.md:1199-1206`) and turns "new
  trusted reduction rules" into "no trusted reduction rules": the float note itself says that would
  "improve assurance even if every result stayed the same" (`float.md:714-715`).
- **Cost to everything else:** primitive hashes become definition hashes, so every dependent hash
  changes once and the runtime bindings and caches are rebuilt (`float.md:1203-1206`). Hash
  stability isn't a goal.

### Summary table

| | Trusts (kernel) | Build size | Speed, known values | Speed, unknown | Provable | New axioms |
|---|---|---|---|---|---|---|
| (a) | 11 rules | none | fast | n/a | no laws | none |
| (b) | 11 rules + each law | ~1 stage | fast | n/a | listed laws only | yes, one per law |
| (c) | 11 rules + 11 spec axioms | model + laws | fast | as (d) | any | 11 |
| (d) | natives = definitions (tested in-kernel) | model + laws | fast | folded/opaque | any | none |

## 7. Recommendation

**Option (d)**, with this model.

**Exact, then round, in one place.** Every finite double is a whole number of units of 2^-1074
(the smallest subnormal): a normal double `1.f × 2^(e - 1023)` is `(2^52 + f) × 2^(e - 1075)` and
`e ≥ 1` [inferred from the binary64 layout, which `Float.toIntFrom` already decodes, [checked]
`Float.sw:540-555`]. So define

- `Float.units (x: Float): Int` — a finite double's value in units of 2^-1074, exact (both zeros
  are `0`);
- `Float.roundScaled (n: Int) (e: Int) (zeroSign: Bool): Float` — the double nearest `n × 2^e`,
  ties to even, `±∞` past the largest, and a zero's sign chosen by the caller. This is what Rocq's
  spec calls `binary_normalize`: `of_uint63_spec` is `Prim2SF (of_uint63 n) = binary_normalize prec
  emax (to_Z n) Z0 false` [read, `FloatAxioms.v:73`].

Then the operations are the IEEE case table (NaN, infinities, zeros) around one call each:

- `add x y` = `roundScaled (units x + units y) (-1074) …` for finite `x`, `y`, the zero sign being
  `+` unless both are `-0.0` (ECMAScript's rule, §3);
- `sub x y` = `add x (neg y)` (ECMAScript defines `Number::subtract` this way [read]);
- `mul x y` = `roundScaled (units x × units y) (-2148) …`;
- `ofInt n` = `roundScaled n 0 False`, `ofNat` likewise — which gives the deferred
  `toInt`/`ofInt` theorem a model to be proved from (`float.md:1150-1156`);
- `div` needs rounding of a fraction (an integer quotient and whether the remainder is zero, below
  or above half: Flocq's "location"); `rem`, `floor`, `ceil`, `trunc` and `round` are exact and
  can be written directly over the bits, as `toInt` is.

**Why this model:** laws about order reduce to two facts about one function. `units` is monotone
(and injective apart from the two zeros), and `roundScaled` is monotone and returns `x` for
`n = units x`. The trigger law is then: `units d ≥ 0`, so `units s + units d ≥ units s`, so
`roundScaled … ≥ roundScaled (units s) … = s`, plus the case table of §3 for the specials and the
zero sign. Lean's unpacked model (align exponents, then normalise per operation, §4.2) is faster
to run but every law has to see through the alignment; Flocq's real-number view needs real numbers,
which Stitchwort doesn't have [inferred].

**What std proves.** Only laws a program needs, plus a short core that makes them easy: `units`
monotone, `roundScaled` monotone and the identity on doubles; `add` commutative; `sub = add ∘ neg`;
`x + (-0.0) = x`; and the trigger's monotonicity `0.0 <= d → s <= s + d`. More when a program asks
(backlog only with a concrete trigger).

**Keep the native.** The `f64` native stays for speed, and the runtimes don't change at all. A
kernel built with float natives off computes the definitions, which is what the gate compares.

**Test the definitions against hardware harder than today.** Beyond `float_paths.rs`'s edge set:
cases built to hit rounding boundaries (ties, results just under and over a power of two, overflow
at exactly the halfway point past `MAX_VALUE`, subnormal results). Lean uses Berkeley TestFloat and
UCBTest for this [read, PR #14079]; whether either can be used here (licence, format) is open.

## 8. Staging

Each stage is one lane; each ends with the named tests passing.

1. **`roundScaled`, `units`, `add`, `sub` as definitions.** The model functions in
   `std/Float/Float.sw` (or a sibling file); `Float.add` and `Float.sub` become definitions with
   the `f64` computation as their kernel natives (the `FloatOp` reduction moves from "primitive"
   to "native" for these two); hashes and bindings updated. Tests: the gate passes with float
   natives on and off; the definitions computed with natives off agree with Node on the
   `float_paths.rs` edge set and on rounding-boundary cases; kernel steps per `add` with natives
   off measured. Exit question: opaque or transparent definitions (an implementation choice).
2. **The laws.** `units` monotone and injective off the zeros; `roundScaled` monotone and the
   identity on doubles; then `Float.addMonotoneRight : 0.0 <= d → s <= s + d`, `Float.addComm`,
   `Float.subAddNeg`, `Float.addNegZero`. The trigger proof drops its hypothesis and uses the law.
   Unit tests stay beside the theorems.
3. **`mul`, `ofInt`, `ofNat`** through `roundScaled`; the general `toInt`/`ofInt` theorem
   (`float.md:1150-1156`).
4. **`div`, `rem`, `floor`, `ceil`, `trunc`, `round`.** After this, no float primitive has a
   reduction rule; DESIGN.md §13's float row and `FLOAT_CONTRACT`'s role are rewritten (the
   contract still governs the runtimes, §3.3 of the float note).

Stages 3 and 4 have no program waiting for them; they can wait for one, but leaving a mix of
"definition with native" and "primitive with rule" is a permanent two-mechanism cost, so doing
them soon after is reasonable [inferred].

## 9. Decisions

**D1363 — Should std be able to prove laws about rounding operations, and by what mechanism?**
The rounding operations have no laws today. Options:

- (a) No laws; programs carry hypotheses.
- (b) A few trusted laws, each an axiom, tested against hardware.
- (c) A model in the logic plus one axiom per primitive (Rocq).
- (d) The primitives become definitions over the bits, with the hardware as a native (Lean,
  Isabelle; how `Nat` already works). **[Recommended]**: no axiom; laws provable; speed on known
  values unchanged; the kernel trusts less than today.

**D1364 — What does the trigger proof do until the law is proved (end of stage 2)?** Options:

- Keep the hypothesis until then; nothing is added to the trust base. **[Recommended]**
- Add `0.0 <= d → s <= s + d` now as an axiom, and delete it when stage 2 proves it.

**D1365 — The shape of the model.** Options:

- Exact, then round: every finite double as a whole number of units of 2^-1074, and one rounding
  function used by `add`, `sub`, `mul`, `ofInt` and `ofNat`. Simplest to prove order laws from;
  slower when computed without natives. **[Recommended]**
- Lean's shape: unpack to sign/mantissa/exponent, align, compute, normalise, per operation. Faster
  to compute; each law has to reason through the alignment.
- A port of Flocq's `binary_float` and proofs. Most proved results, but its proofs are about real
  numbers, which Stitchwort doesn't have.

**D1366 — Which laws std proves.** Options:

- The trigger's law and a small core (`add` commutative, `sub` is `add` of `neg`, `x + (-0.0) =
  x`, and the two rounding facts), then more only when a program needs one. **[Recommended]**
- A general library now (error bounds, Sterbenz, more): a project of its own, with no program
  asking for it.

## Appendix A: scripts run

Both are in the session scratchpad (`flscripts/monotone.js`, `flscripts/laws.js`), run with Node
22.23.3. Both compare doubles in the canonical-NaN total order, computing `Float.orderKey`'s key
from the bits (`OfNat bits` with the sign clear, `-(magnitude + 1)` with it set, the NaN as
`0x7FF8000000000000`), and compare equality with `Object.is`.

```
$ node monotone.js
checked 4999773 pairs with 0.0 <= d, failures 0

$ node laws.js
x + 0.0 = x                  FALSE, e.g. -0, 0, 0
x + (-0.0) = x               no counterexample found
x + y = y + x                no counterexample found
x * y = y * x                no counterexample found
x - y = x + (-y)             no counterexample found
-(x + y) = (-x) + (-y)       FALSE, e.g. 0, -0, 0
0 <= d -> s - d <= s         FALSE, e.g. 0, NaN, 0
0 <= d -> s <= s + d         no counterexample found
x <= y -> x + z <= y + z     FALSE, e.g. -Infinity, 0, Infinity
```

`laws.js` tries every triple of a 15-value edge set, then 300,000 random triples of bit patterns.
"No counterexample found" is evidence, not proof.

## Sources

Read in full:

- G. Bertholon, É. Martin-Dorel, P. Roux, "Primitive Floats in Coq", ITP 2019, LIPIcs 141, 7:1–7:20:
  https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.7/LIPIcs.ITP.2019.7.pdf
- S. Boldo, G. Melquiond, "Flocq: A Unified Library for Proving Floating-point Algorithms in Coq",
  ARITH 2011: https://inria.hal.science/inria-00534854

Read in part (§1–6):

- S. Boldo, J.-H. Jourdan, X. Leroy, G. Melquiond, "Verified Compilation of Floating-Point
  Computations", J. Automated Reasoning 54(2), 2015: https://inria.hal.science/hal-00862689

Source files, specifications and pages read:

- Rocq `FloatAxioms.v`: https://github.com/rocq-prover/rocq/blob/master/theories/Corelib/Floats/FloatAxioms.v
- Rocq reference manual, primitive objects: https://rocq-prover.org/doc/master/refman/language/core/primitive.html
- Rocq issues #12483, #16096, #17871: https://github.com/rocq-prover/rocq/issues/12483 ,
  https://github.com/rocq-prover/rocq/issues/16096 , https://github.com/rocq-prover/rocq/issues/17871
- Lean `Float.lean`: https://github.com/leanprover/lean4/blob/master/src/Init/Data/Float/Float.lean ;
  `Model/Float.lean`: https://github.com/leanprover/lean4/blob/master/src/Init/Data/Float/Model/Float.lean ;
  `Model/Unpacked/Operations/Add.lean` and `Model/Unpacked/Basic.lean` in the same directory
- Lean PRs #14079 (`Float.Model`) and #14091 (`Float` is no longer opaque):
  https://github.com/leanprover/lean4/pull/14079 , https://github.com/leanprover/lean4/pull/14091
- Lean reference, floating-point numbers: https://lean-lang.org/doc/reference/latest/Basic-Types/Floating-Point-Numbers/
- Mathlib `Data/FP/Basic.lean`: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/FP/Basic.lean
- Isabelle AFP `IEEE_Floating_Point`: https://www.isa-afp.org/entries/IEEE_Floating_Point.html ;
  its `Double` theory: https://www.isa-afp.org/browser_info/current/AFP/IEEE_Floating_Point/Double.html
- HOL4 `binary_ieeeScript.sml`: https://github.com/HOL-Theorem-Prover/HOL/blob/develop/src/floating-point/binary_ieeeScript.sml
- F\* `FStar.Float64.fsti`: https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Float64.fsti
- Why3 `ieee_float`: https://www.why3.org/stdlib/ieee_float.html
- Agda built-ins (Floats): https://agda.readthedocs.io/en/latest/language/built-ins.html
- ECMAScript, the Number type and `Number::add`/`Number::subtract` (§6.1.6.1):
  https://tc39.es/ecma262/multipage/ecmascript-data-types-and-values.html
- Rust RFC 3514, float semantics: https://rust-lang.github.io/rfcs/3514-float-semantics.html
- WebAssembly core spec, numerics: https://webassembly.github.io/spec/core/exec/numerics.html
- WebKit bug 194853, dropping x87: https://bugs.webkit.org/show_bug.cgi?id=194853
