# Proposal: laws about `Float`'s rounding operations

**Status:** accepted, 26 October 2026 (D1363 (d), D1368 (i); D1364–D1366 and D1369 as recommended). A research and design note; nothing here changes the
compiler. Written against commit `50214b95`. Decisions D1363–D1366 and D1368–D1369 are
[at the end](#11-decisions), each with a recommended option, for Matt to decide.

Labels: **[checked]** (read in this repository, `file:line`), **[inferred]** (my reasoning, not
stated anywhere or not tested), **[ran]** (run while writing this: Node 22.23.3 and the release
`stitchwort` binary on macOS/arm64; the scripts are in [Appendix A](#appendix-a-scripts-run)),
**[read]** (read in the linked source; quoted verbatim where the wording matters). Papers marked
**read in full** were read end to end, not just their abstracts. Lean source files were read on
`master` on 26 October 2026; line numbers are from that version.

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
operation *is* a definition over bits, with no axiom, and compiled code uses the hardware instead.
Lean's kernel never runs the hardware version: it computes floats through the definition, and
accelerates only `Nat` ([§4.2](#42-lean-4)).

**Recommendation: option (d), no axioms, with the hardware used only while programs run.** Give
each rounding operation a real Stitchwort definition over the bits. When the kernel *checks*
(including conversion, where `rfl` proofs are decided), it computes floats with those definitions,
on top of the existing `Nat` natives; the `f64` code is used only while a program or test runs,
and by the runtimes. This is Lean's position, trust position (i) of
[§7](#7-what-the-kernel-trusts). Then:

- nothing new is assumed, and no float code is in the kernel's trusted base: a mistake in a
  definition is a wrong answer, which the tests against hardware catch, not a proof of `False`;
- any true law can be proved, and std proves the few that programs need, starting with the
  trigger's;
- closed float computations *inside proofs* get slower (a few milliseconds per operation, measured
  on a stand-in, [§7](#7-what-the-kernel-trusts)); programs and tests don't.

Keeping the `f64` code as a kernel native that takes part in conversion, as `Nat.add` has one,
would keep checking fast but put a new, large agreement in the trusted base: on every input, the
native must equal its definition, or the kernel proves `False`. Today's primitives are trusted
less than that ([§7.1](#71-today-what-a-wrong-rule-can-and-cant-do)).

The model should be the simple "exact, then round" one: every finite double is a whole number of
units of 2^-1074, so `x + y` is "add the two whole numbers exactly, then round to the nearest
double". Two rounding functions, `roundScaled` for `n × 2^e` and `roundRatio` for fractions, share
one specification and one core ([§8](#8-recommendation-the-model)). Laws come from a few facts
about rounding, stated with the sign of zero explicit ([§9](#9-the-central-lemmas-and-the-trigger-proof)).
Four stages; the trigger law is proved at the end of the second ([§10](#10-staging)).

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
- **Conversion.** The kernel's test of whether two terms are equal by computation ("definitional
  equality"). An `rfl` proof of `a = b` is accepted exactly when `a` and `b` convert, so whatever
  the kernel computes with during conversion decides which equations are theorems.
- **Trusted reduction rule.** A rule by which the checker *computes* (`0.1 + 0.2` becomes
  `0.30000000000000004`) whose correctness the checker can't check. For a constant with *no*
  definition, a wrong rule gives wrong answers but can't prove `False`, as long as it is a fixed
  function of its arguments ([§7.1](#71-today-what-a-wrong-rule-can-and-cant-do)).
- **Native.** In Stitchwort, a fast Rust implementation of an *ordinary definition*, used by the
  evaluator instead of unfolding it, including during conversion. It must give exactly what the
  definition gives: if it disagrees on some input, one side of an equation can be computed by the
  native and the other by unfolding, and the kernel then proves `False`. Tests compare them, and
  switching natives off makes the definition run instead.

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

**Natives and primitives both take part in conversion.** The evaluator's `unfold_now` runs a float
primitive or native (`float::run`) and then a number native (`native::run`) *before* a
definition's case tree, whenever the arguments are known ([checked]
`crates/core/src/value.rs:1650-1668`). Conversion (`conv`, `value.rs:2163`) compares values the
evaluator produced, so it sees the native's answer, never the unfolding, on known arguments
[checked: `conv_step`, `value.rs:2298-2420`, has no path that bypasses evaluation]. `docs/core.md`
says the same of `Nat`: "conversion treats `3` and `Succ 2` as equal" and the natives "run natively
when all their number arguments are numbers" ([checked] `native.rs:5-7`, `docs/core.md:230`). The
float gate's program proves `theorem sumTenths: 0.1 + 0.2 = 0.30000000000000004 := rfl`, which the
kernel accepts by computing the primitive during conversion ([checked]
`crates/driver/src/float_gate.rs:50`). The only exception is the case-tree congruence rule,
which skips natives and float definitions (`value.rs:2586-2587`).

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
implementations are part of the trusted base (DESIGN.md §13): a bug in one could make the kernel
accept `2 + 2 = 5`. Each must compute exactly what its definition computes" ([checked]
`crates/core/src/native.rs:9-14`). `Int` has no kernel natives at all: its operations are
definitions over `Nat`'s ([checked] `DESIGN.md:951`; decision K1,
`docs/proposals/integers.md:532-536`). The float exact operations (`neg`, `abs`, `isNaN`, `toInt`
…) are definitions with natives too, bound by content hash ([checked] `float.rs:25-35`), so they
are already trusted the way `Nat`'s natives are.

**The gate already compares definitions with natives.** Stage 1a's gate runs every check with the
float natives off and the number natives on, comparing whole normal forms, proofs included
([checked] `float.md:193-209`; `Builtins::disable_float_natives`, `crates/core/src/native.rs:152`,
`float_def` at `:176-188`). It now has 1,121 checks per run ([checked] `float.md:103`). There is
no command-line switch for it: natives are turned off only through the Rust API, in tests and the
gate, and the test cache's mode key records `disable_natives` but not `disable_float_natives`
([checked] `crates/driver/src/driver.rs:874-883`, `float_gate.rs:286-287`).

**Running versus checking.** The evaluator knows when a program or test is running rather than a
definition being checked: `Erasure::running` sets a flag that `program_running` reads ([checked]
`crates/core/src/erase.rs:118-135`), and the test runner and `run_main` set it
(`crates/driver/src/driver.rs:1238`, `:1299`, `:1346`; `crates/driver/src/run.rs:304`, `:497`).

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

**The law covers `d` = NaN, and application statements usually shouldn't.** Because the total
order puts the NaN on top, `0.0 <= NaN` holds, so this general law also says something (true, and
trivial) about adding the NaN. Where an application means "a non-negative amount", its statements
should say *finite and non-negative*, `d.isFinite ∧ 0.0 <= d`, which is what the words mean; the
general law then applies with the finiteness unused. The triggering program already states it that
way: its well-formedness predicate requires every duration to be finite and `0.0 <=` [checked in
that program's source, which is not in this repository]. So the general law serves it either way.

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
[§9](#9-the-central-lemmas-and-the-trigger-proof) gives the proof the model will carry.

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
- **What came before: kernel acceleration of a definition.** Coq's first machine integers used
  "the so-called retro-knowledge approach, which consisted in developing a reference
  implementation of 31-bit integer operators in Coq … then optimizing their evaluation … by
  replacing the considered Coq operator on-the-fly with the corresponding hardware operator. The
  implicit assumption here is that both implementations match" (§2.1). That is exactly a
  Stitchwort native taking part in conversion (trust position (ii) of [§7](#7-what-the-kernel-trusts)),
  and the closest precedent for it. It was replaced by primitive integers for "a compact
  representation of integers, and making explicit the axioms that specify the primitive operators".
  Stitchwort already has a compact representation (a `Float` is a record holding a `Nat` literal,
  `float.md:830`), so the first reason doesn't apply to it [inferred]; the second, that the
  matching assumption was implicit, does.
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
contradiction by the axiom that says they agree. If Stitchwort keeps the `f64` code as a native that
takes part in conversion, the same model bug is *still* a proof of `False`: on the input where they
disagree, the kernel computes one side of an equation with the native and the other through a
general theorem proved from the definition. No axiom is involved, but the native is in the trusted
base in the axiom's place. The natives-off gate would find the bug only if it tests that input
(both Rocq bugs were on edge inputs, `1 <= 0` and the zeros, which the gate's edge set covers
[inferred]). Only if the kernel never uses the native while checking is the same bug merely a wrong
`add`, caught by the tests against hardware [inferred; argued in §7].

### 4.2 Lean 4

`Float` used to be opaque. Since June 2026 it isn't: PR leanprover/lean4#14079 added `Float.Model`
and #14091, "`Float` is no longer opaque", made `Float` a structure over it and "redefine[d] `add`,
`sub`, `mul`, `div`, `sqrt`, `abs`, `neg`, `isNaN`, `isInf`, `isFinite`, `le`, `lt`, `beq`, `ofInt`,
`ofNat` … to delegate to their `Float.Model` counterparts. This does not change anything about
compiled code; compiled code uses the accelerated functions from the runtime as before" [read, PR
descriptions]. The current source [read, `src/Init/Data/Float/Float.lean:76-77`]:

```
@[extern "lean_float_add"] def Float.add : Float → Float → Float :=
  fun a b => .ofModel (a.toModel + b.toModel)
```

The file's own description: "From the point of view of Lean's logic, `Float` is equivalent to
`Float.Model` … Some of the operations on `Float` are defined in terms of their `Float.Model`
counterparts, while others are opaque to Lean's kernel" [read, `Float.lean:31-35`]; the opaque ones
are the transcendental functions, e.g. `@[extern "sin"] opaque Float.sin` (`Float.lean:344`), and
`toString` (`:193`). `Float.Model` "is defined as the type of `UInt64` with the additional
restriction that bit patterns encoding a `NaN` must be exactly a chosen canonical `NaN`" — the same
shape as Stitchwort's `Float` — and its operations unpack to sign, mantissa and exponent, compute,
round and repack [read, `src/Init/Data/Float/Model/Float.lean`; `Unpacked/Operations/Add.lean`
aligns the two exponents, adds the signed mantissas exactly, then calls `normalize`, which rounds].

**Lean's kernel computes floats through the model, never through the C code.** Three pieces of
evidence [read]:

- The kernel's only built-in arithmetic is on `Nat`. `type_checker::reduce_nat`
  (`src/kernel/type_checker.cpp:668-698`) recognises `Nat.succ`, `Nat.add`, `sub`, `mul`, `pow`,
  `gcd`, `mod`, `div`, `beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft` and `shiftRight` on literals,
  and nothing else. It is used both in `whnf` (`:728`) and in `lazy_delta_reduction`, the
  definitional-equality check (`:1068-1080`), so Lean's `Nat` acceleration takes part in conversion,
  just as Stitchwort's `Nat` natives do. There is no float case.
- `@[extern]` and `@[implemented_by]` only tell the compiler what to call. The `implemented_by`
  documentation: "Instructs the compiler to use a different function as the implementation of a
  function. With the exception of tactics that call native code such as `native_decide`, the kernel
  and type checking are unaffected. … The provided implementation is not checked to be equivalent
  to the original definition. This makes it possible to prove `False` with `native_decide` using
  incorrect implementations. For a safer variant … see `@[csimp]`, which requires a proof that the
  two functions are equal" [read, `src/Lean/Compiler/ImplementedByAttr.lean:15-43`].
- The one route from compiled code into proofs is explicit and reported: "proofs by native
  evaluation introduce a dedicated axiom for each computation that is asserted by the compiled
  code. … These axioms track proofs that depend on the correctness of the entire compiler, and not
  just on the much smaller kernel", and "The native_decide tactic creates a bespoke axiom for each
  invocation … This allows each axiom to be audited for the precise statement that it proves"
  [read, Lean reference, Axioms].

So in Lean the trust that "the C implementation (`@[extern]`) agrees with the definition" is not
kernel trust: a disagreement makes compiled programs compute something other than what was proved
about them, but cannot make the kernel accept `False` unless `native_decide` is used, and then an
axiom shows it. "The logical model is extensively empirically tested against the floating-point
operations on all supported platforms" [read, Lean reference], using "difficult test cases
generated using Berkeley TestFloat and UCBTest" [read, PR #14079]. Stitchwort's native differs in
kind: it runs inside the kernel during conversion, like Coq's retro-knowledge (§4.1), not beside
it like Lean's `@[extern]`. I did not run Lean to time a kernel-checked `decide` on a float
equation; that it reduces through the model follows from the three points above [inferred].

Lean does **not** provide laws: "It is not a goal of this development to serve as the basis for a
general-purpose floating-point library or to have any direct lemmas written about it at all.
Rather, users … should prove that the operations defined here are equivalent to the operations
defined in the separate library and then transfer lemmas" [read, `Model/Float.lean`]. That is a
separation of the type programmers use (`Float`), the executable model (`Float.Model`) and the
reasoning layer (a separate library, linked by an equivalence proof), which [§8](#8-recommendation-the-model)
borrows. Mathlib's own older float type, `Mathlib/Data/FP/Basic.lean` ("Implementation of
floating-point numbers (experimental)"), was deprecated on 2026-10-02 with "no replacement" [read].
A code search of Mathlib for `Float.Model` found nothing [ran: `gh search code`].

### 4.3 Flocq

Boldo and Melquiond, "Flocq: A Unified Library for Proving Floating-point Algorithms in Coq", ARITH
2011 [**read in full**]. Floats are real numbers `m · β^e`; a format is described by a function `ϕ`
from a number's magnitude to its exponent, and rounding is `Zrnd(scaled mantissa) · β^cexp(x)`
(§III-D, III-E). Laws are theorems: rounding is monotone (Theorem 1 and §III-A's definition of a
rounding predicate as total and monotone), Sterbenz's exact subtraction (Theorem 4), relative error
(Theorem 5), and "when x + y rounds to zero … x + y is mathematically equal to zero" (Theorem 9).
For computation, Flocq locates the exact result between two floats with a "location" (exact, below
half, half, above half), which "are similar to the usage of the round and sticky bits" (§IV-A).
The location is what lets one rounding core serve every operation, division included: an operation
only has to say where its exact result lies between two neighbouring candidates.

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
  here..." [read, `Double.html`]. That is option (d) with trust position (i): definitions in the
  logic, hardware in generated code.
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

**The invariant.** On every supported target, each runtime computes exactly the IEEE binary64
round-to-nearest-even result, with the NaN canonical. That is an *invariant the differential tests
check continuously*, not something the kernel takes on faith: `float_paths.rs` compares the
kernels, the Rust runtime and Node on canonical bits for every operation ([checked]
`float_paths.rs:1-20`), and with option (d) the kernel side of that comparison is the definition.
The published specifications below are the reason to expect the invariant to hold, and the list
of known ways it has failed elsewhere says where to aim the tests.

| Runtime | What its specification promises | Status |
|---|---|---|
| Kernel and Rust runtime (`f64`), native backend (calls the runtime) | Rust RFC 3514: "Primitive operations on floating-point types generally produce results that exactly match IEEE 754-2008", with roundTiesToEven, "without abruptUnderflow/flush-to-zero"; NaN sign and payload non-deterministic; Rust "does not support executing floating-point operations with alternative rounding modes" [read] | Expected exact on our targets (x86-64, aarch64, wasm32) except NaN bits, which we canonicalise. The RFC's exceptions are i586 without SSE2 ("operations are internally computed with a different precision") and 32-bit ARM NEON, which "always flush-to-zero" [read]; neither is a Stitchwort target [inferred] |
| WebAssembly kernel (the playground) | "Floating-point arithmetic follows the IEEE 754 standard … All operators use round-to-nearest ties-to-even"; a NaN result's "sign is non-deterministic" [read, WebAssembly spec, numerics] | Expected exact except NaN bits |
| JS | ECMAScript: Number values are "the double-precision floating point IEEE 754-2019 binary64 values … except that the … distinct NaN values … are represented in ECMAScript as a single special NaN value"; `Number::add` "performs addition according to the rules of IEEE 754-2019 binary double-precision arithmetic" with ties to even [read, §6.1.6.1] | Expected exact; engines are tested, not proved |

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

Every option keeps the runtimes on hardware and keeps the §3.3 contract. What changes between the
options is what the definition says and whether the *kernel* uses the hardware code
([§7](#7-what-the-kernel-trusts)). If a runtime breaks the invariant, a proved theorem is still true
of the definition, but a compiled program no longer computes what was proved about it.

## 6. The options

### (a) No laws (today)

- **Trusts:** the 11 reduction rules on known values (`DESIGN.md:953`); for consistency, only that
  each is a fixed function ([§7.1](#71-today-what-a-wrong-rule-can-and-cant-do)).
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
  just for known values. Worse, a law and the reduction rule must now agree: a rule bug that
  breaks a trusted law on some input is also `False`. Testing can't be exhaustive (2^128 pairs per
  binary law); Rocq's two wrong axioms both shipped in releases before being found
  ([§4.1](#41-rocq-primitive-floats); #12483 was reported against Coq 8.11, #16096 fixed in 8.15.2).
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

### (d) No axioms: the primitives become definitions

Replace each bodyless primitive by a Stitchwort definition over the bits. The `f64` computation
stays for the runtimes; whether the *kernel* also uses it, as a native, is the separate choice of
[§7](#7-what-the-kernel-trusts) (D1368). This is Lean's design since June 2026 and Isabelle's.

- **Trusts:** depends on that choice. If the kernel never uses float natives while checking
  (position (i), recommended), no float code is in the trusted base: the definitions run on the
  existing `Nat` natives, and a wrong definition is a wrong `add`, caught by the four-path test
  against Node and the hardware. If the `f64` code is a kernel native (position (ii), how `Nat.add`
  works), the kernel trusts that native = definition on every valid input: a disagreement anywhere
  proves `False` (§4.1's argument), and the natives-off gate is a test of that, not a guarantee.
  In both, the reduction rules disappear from DESIGN.md §13; `toText` stays a primitive with no
  rule.
- **Size:** largest. Two rounding front ends over one core and the operations
  ([§8](#8-recommendation-the-model)); tests of the definitions against the hardware on hard
  cases; proofs of whichever laws std provides ([§9](#9-the-central-lemmas-and-the-trigger-proof)).
  Each operation is a few dozen lines; rounding is the hard part, done once. Lean's `Round.lean` is
  7.7 KB and `Add.lean` 1.3 KB [read: Lean tree sizes].
- **Checking speed:** see [§7.3](#73-three-trust-positions). With float natives in the kernel,
  unchanged on known values; without, each closed operation in a proof costs milliseconds.
  - *Unknown values:* a definition stuck on unknown bits stays folded, like the primitive today
    (the unfolding policy, [checked] `docs/core.md:213`). One risk: conversion compares two
    *different* non-recursive definitions stuck on a `case` by their case trees ([checked]
    `docs/core.md:218`), which for big float definitions could be slow when two float terms
    differ. Making them opaque (`opaque def`, [checked] `docs/core.md:162-170`) avoids that, with
    the law files `unfolding` them [inferred; stage 1 decides].
- **Users can prove:** any true law. Std proves the common ones once (§9).
- **Fit:** it completes §6.3's plan (`float.md:1199-1206`). With position (i) it also turns
  "new trusted reduction rules" into "no trusted float code in the kernel", which the float note
  said would "improve assurance even if every result stayed the same" (`float.md:714-715`).
- **Cost to everything else:** primitive hashes become definition hashes, so every dependent hash
  changes once and the runtime bindings and caches are rebuilt (`float.md:1203-1206`). Hash
  stability isn't a goal.

### Summary table

| | Kernel can prove `False` if … | Build size | Speed, known values in proofs | Provable | New axioms |
|---|---|---|---|---|---|
| (a) | a rule isn't a fixed function (§7.1) | none | fast | no laws | none |
| (b) | a law is wrong, or a rule breaks one | ~1 stage | fast | listed laws only | yes, one per law |
| (c) | the model ≠ the hardware anywhere | model + laws | fast | any | 11 |
| (d) + (i) | never, from float code | model + laws | ms per operation | any | none |
| (d) + (ii) | a native ≠ its definition anywhere | model + laws | fast | any | none |

## 7. What the kernel trusts

### 7.1 Today: what a wrong rule can and can't do

Today each rounding operation is a bodyless constant with one reduction rule: on known valid bits,
compute `f64` and canonicalise the NaN; otherwise stay stuck and compare structurally
([checked] `float.rs:769-830`, `docs/core.md:253`). Nothing else in the logic says anything about
`Float.add`: there is no definition, no axiom and no law.

So for *consistency* the rule needs only to be a fixed function of the argument bits that returns
valid bits. Then the system behaves exactly as if `Float.add` had been *defined* as that function
(every finite function on 64-bit numbers is definable), so it is as consistent as the logic without
it [inferred: this is the standard argument that a constant with a deterministic δ-rule is a
conservative extension]. The rule meets that condition by construction: `f64` addition is
deterministic apart from NaN bits, which `canonical_bits` fixes ([checked] `float.rs:133`), and
`float_value` builds a valid record. If the rule computes the wrong IEEE answer, the kernel proves
wrong *facts about IEEE* (`0.1 + 0.2 = …` with the wrong bits), but not `False`. That is a
*meaning* error, the same kind as a runtime computing the wrong answer, and the four-path test is
what catches it.

Proving `False` from a reduction rule needs a second way of computing the same constant for it to
disagree with, such as a definition; for the rounding primitives none exists. The float exact
operations are different: they *are* definitions with natives in conversion ([checked]
`float.rs:25-35`, `value.rs:1657-1660`), so they already carry `Nat`-style trust.

### 7.2 What option (d) changes

Option (d) gives `Float.add` a definition. From then on the definition is what proofs reason
about: laws are proved from it, by unfolding it on unknown values. That is the point, but it means
that any other way of computing `Float.add` on known values must agree with the definition there,
or the two ways together prove `False`. Concretely, if a native gives `r1` for `add a b` and the
definition gives `r2 ≠ r1`: `rfl` proves `add a b = r1` (the native fires during conversion); any
general law, or simply `theorem t (x y: Float): add x y = addDefinition x y := rfl` instantiated
at `a b`, followed by computing `addDefinition a b` (which has no native), gives
`add a b = r2`; and `r1 ≠ r2` is decidable on bits [inferred; this is the argument `native.rs:12`
makes for `Nat`: "a bug in one could make the kernel accept `2 + 2 = 5`"].

So the trust needed with a kernel native is **"native = definition on every known valid input"**,
the same kind of trust `Nat`'s natives already carry. It replaces "primitive = IEEE" as the
consistency condition, and unlike that one it can be tested inside the kernel: switch the float
natives off and compare, which the gate already does ([checked] `float.md:193-209`).

**Is that less trust than today?** No. It is different, and for consistency it is more:

- Today's consistency condition, "the rule is a fixed function", is met by construction. Today's
  *meaning* condition, "the rule is IEEE", is tested, and a failure is a wrong answer.
- With a kernel native, the native is still the `f64` code, so "native = definition" holds exactly
  when "`f64` = IEEE" (today's meaning condition) *and* "definition = IEEE" (new) both hold on that
  input, or both fail the same way. Both are now consistency conditions: a bug in either, on any of
  2^128 input pairs, is a proof of `False`. The definition is a few hundred lines of new rounding
  code, the kind that went wrong twice in Rocq (§4.1).
- What the native buys is that the condition is checkable in the kernel, by sampling. Testing is
  strong evidence, not exhaustive: `Nat`'s natives are tested "on every small input and on random
  larger ones" ([checked] `docs/core.md:232`), and float natives could be tested the same way, but
  2^128 pairs can't all be tried.

Without a kernel native, the definition is the *only* way the kernel computes `Float.add`. Then
nothing float-specific can prove `False`: the remaining trust is in the `Nat` natives the
definition runs on, which the kernel trusts already. "Definition = IEEE" and "runtime = definition"
remain, as meaning conditions, tested by the four-path test, exactly as "rule = IEEE" is today.
That is genuinely less consistency trust than today (a little: today's is already small), and the
meaning trust moves from Rust's `f64` code to a readable definition that laws are proved from.

### 7.3 Three trust positions

**(i) Lean-style: the kernel always uses the definition; hardware only while running.** Float
natives (the new ones and today's exact-operation natives) fire only when `program_running()` is
set ([checked] `erase.rs:129-135`), i.e. in tests and runs, and never while a definition is checked
or the elaborator unifies. The runtimes keep the hardware. This is Lean's split between the kernel
and compiled code (§4.2), with the evaluator's run mode playing the compiled code's role.
Implementation: one condition in `Builtins::float_def` ([checked] `native.rs:176-188`) [inferred].

Cost, measured on a stand-in [ran, `pow.sw` in Appendix A]: no model exists yet, so I timed a
computation of the same shape as one rounding step with the float natives unavailable: build
`2^2046` with `Nat.pow` (2,046 native multiplications, [checked] `Arith.sw:517-519`), find the bit
length of a 2,047-bit number by halving it (2,047 native divisions) and divide by `2^1000`. One
hundred of them, each checked by `rfl`, took 0.87 s against 0.15 s for a file without them, so
about **7 ms per operation** on the release binary [ran]. A real `add` is about one such step, a
`mul` about two (its integers are twice as long, [§8](#8-recommendation-the-model)) [inferred].

- *`rfl` on `0.1 + 0.2`:* about 7 ms instead of microseconds [inferred from the stand-in].
- *Closed float computations in proofs:* rare today. 19 Stitchwort files import `Float`
  ([ran] `git grep`), mostly examples with a few `rfl` rows each. A proof that computes a
  thousand float operations on known values would take seconds. Tests and `main` run with
  natives, so unit tests are unaffected.
- *The four-path test's kernel paths:* about 35 values (25 edges, 10 random; [checked]
  `float_paths.rs:32-58`, `:296`), so 1,225 pairs, each with the five binary rounding operations
  among its 17 results (`:210`): about 6,100 rounding operations per kernel, about 45 s at the
  stand-in's rate, against a 10-second lane budget [inferred]. If that path evaluates in run mode,
  natives fire and it costs what it does today; then a separate, smaller definitions-versus-hardware
  test is needed for the kernel side.
- *Making it cheaper:* most of the stand-in's time is the two linear loops, `Nat.pow` and bit
  length. Natives for `Nat.pow`, shifts and bit length, which Lean's kernel has for `pow`,
  `shiftLeft` and `shiftRight` ([read] `type_checker.cpp:686`, `:695-696`), would make each a
  single step. They are `Nat` natives: small, exact, and tested like the existing ones [inferred].

**(ii) Kernel natives trusted, with the natives-off gate as defence in depth.** The `f64` code is
each definition's native, in conversion, as for `Nat`. Checking speed is unchanged. The kernel
trusts native = definition everywhere (§7.2); the gate samples that. This is Coq's retro-knowledge
(§4.1), which Coq left partly because "the implicit assumption here is that both implementations
match".

**(iii) Natives for fast checking, plus a final check with float natives off.** Day-to-day
checking uses (ii); anything accepted into std, a release or a shipped build is re-checked with
float natives off, so its trust is (i)'s. In Stitchwort it would need:

- a switch, `stitchwort check --float-natives=off` (and the same for `test`), setting
  `Builtins::disable_float_natives` ([checked] `native.rs:152`), which today only the gate and tests
  set;
- a mode letter for it in the test cache's key, which records only `n` and `c` today ([checked]
  `driver.rs:874-883`), so the two kinds of result aren't confused;
- a daily-tier job (`nix flake check`, [checked] `flake.nix:122`, `:231`) checking std, the
  examples and the AoC solutions with float natives off;
- `stitchwort build` refusing, or warning, unless every proof it depends on has a natives-off
  result in the cache. The local cache is trusted ([checked] `docs/core.md:402`), so this check is
  only as strong as the cache.

Its costs: two meanings of "checked"; a proof that passes with natives on can fail the final check
only by running out of budget, found late; and the final check pays (i)'s price anyway, in CI.

**Recommendation: (i).** Reasons:

1. It is the only position in which a bug in the new rounding code can't prove `False`. That code
   is the part most likely to be wrong (§4.1), and with (i) its bugs are wrong answers that the
   four-path test finds by comparing with hardware.
2. The cost falls only on closed float computation *inside proofs*, which is rare: laws are about
   unknown values, and computations on known values belong in unit tests, which run with natives.
3. One meaning of "checked", no new switch, mode or CI job. (iii) gets (i)'s trust for shipped
   code but adds all three.
4. It matches Lean, which faced the same choice this year, and Isabelle.

If stage 1 measures a closed `add` in checking above about 1 ms even after `Nat` natives for
powers, shifts and bit length, revisit (iii) [inferred threshold: a thousand-operation proof then
takes a second].

## 8. Recommendation: the model

**Option (d)**, with this model.

### 8.1 Three layers

Borrowing Lean's separation (§4.2):

- **`Float`** is the type programmers use, unchanged: `Float.add` and the rest, the operators, the
  exact operations. Each rounding operation's body is one call into the model.
- **`Float.Model`** holds the executable definitions: `units`, `signBit`, the rounding functions,
  and each operation's IEEE case table around one rounding call.
- **`Float.Theory`** holds the reasoning layer: the rounding *specification* (the result is a
  double nearest the exact value, ties to even, with the zero and overflow rules), the proof that
  the model's rounding functions meet it, the central lemmas derived from the specification (§9),
  and the laws. Laws are stated about `Float.add` and the other exported operations, never about
  the model's internals.

Then the executable algorithm can change later behind one proved bridge, "the new rounding meets
the specification", without changing any law's statement or proof: every lemma of §9 is derived
from the specification, not from how the rounding computes [inferred; this is Flocq's split between
`binary_float` functions and their `_correct` theorems, §4.3].

**Should the model's functions be the specification, or a separate faster executable proved
equal?** Exact-then-round (`units` and the rounding functions below) is both simple to prove from
and simple to run, so the recommendation is that it *is* the executable model now. A faster
model (Lean's unpacked form, say) would then be a later change that proves it meets the same
rounding specification, at which point the exact-then-round functions stay as the specification's
reference in `Float.Theory`. Building both now means writing and proving the bridge for a speed
nobody has asked for; keeping the layers separate costs only the namespace boundary. That is
D1369.

### 8.2 Exact, then round

Every finite double is a whole number of units of 2^-1074 (the smallest subnormal): a normal
double `1.f × 2^(e - 1023)` is `(2^52 + f) × 2^(e - 1075)` and `e ≥ 1` [inferred from the binary64
layout, which `Float.toIntFrom` already decodes, [checked] `Float.sw:540-555`]. So define

- `Float.units (x: Float): Int` — a finite double's value in units of 2^-1074, exact (both zeros
  are `0`);
- `Float.signBit (x: Float): Bool` — the sign bit, so `signBit (-0.0) = True`;
- `Float.roundRatio (num: Int) (den: Nat) (scale: Int) (zeroSign: Bool): Float` — for `den > 0`,
  the double nearest `num / den × 2^scale`, ties to even, `±∞` past the largest. Zero rule: if
  `num = 0` the result is the zero with sign `zeroSign`; if `num ≠ 0` and the value rounds to zero,
  the zero takes `num`'s sign (IEEE's underflow rule).
- `Float.roundScaled (n: Int) (e: Int) (zeroSign: Bool): Float := roundRatio n 1 e zeroSign` — the
  double nearest `n × 2^e`. This is what Rocq's spec calls `binary_normalize`: `of_uint63_spec` is
  `Prim2SF (of_uint63 n) = binary_normalize prec emax (to_Z n) Z0 false` [read, `FloatAxioms.v:73`].

**One specification, one core.** `roundRatio` is the general function; `roundScaled` is its
`den = 1` case, so there is one rounding specification and one set of lemmas. Inside,
`roundRatio` picks the result's exponent from the bit lengths of `num` and `den` (or the subnormal
floor), takes the integer quotient `q` and remainder `r` of the scaled numerator by the scaled
denominator `D`, and passes `q` and a *location* to the rounding core: exact if `r = 0`, below half
if `2r < D`, half if `2r = D`, above half if `2r > D` (Flocq's location, §4.3). The core rounds `q`
up or down by the location and the parity of `q`, renormalises if rounding up carried into a new
power of two, and applies overflow and the zero rule. With `den = 1` and `n` already narrow enough,
the division is by a power of two [inferred design; stage 1 writes it].

**The operations** are the IEEE case table (NaN, infinities, zeros, division by zero) around one
call each:

- `add x y` = `roundScaled (units x + units y) (-1074) (signBit x ∧ signBit y)` for finite `x`,
  `y`: the zero sign is `-` only when both are `-0.0` (ECMAScript's rule, §3), and a nonzero sum
  never rounds to zero at this scale;
- `sub x y` = `add x (neg y)` (ECMAScript defines `Number::subtract` this way [read]);
- `mul x y` = `roundScaled (units x × units y) (-2148) (signBit x ≠ signBit y)`;
- `div x y` = `roundRatio (units x × sign (units y)) |units y| 0 (signBit x ≠ signBit y)` for
  finite `x` and finite nonzero `y` (the units' scales cancel);
- `ofInt n` = `roundScaled n 0 False`, `ofNat` likewise — which gives the deferred
  `toInt`/`ofInt` theorem a model to be proved from (`float.md:1150-1156`);
- `rem`, `floor`, `ceil`, `trunc` and `round` are exact and can be written directly over the bits,
  as `toInt` is.

**Sizes** [inferred from the binary64 range]: the largest finite double is just under
2^1024, which is 2^2098 units, so

- `add`'s integers are up to about 2,100 bits;
- `mul`'s product `units x × units y` is up to about 4,200 bits, at scale 2^-2148;
- `div`'s numerator, shifted so the quotient has 53 bits plus a guard bit, is up to about 4,250
  bits (2,100 bits shifted by up to the denominator's length plus 55).

`Nat.mul` and division of numbers of this size are single native steps. The costly parts without
float natives are the linear loops: `Nat.pow 2 k`, which recurses `k` times ([checked]
`Arith.sw:517-519`), up to about 2,100 for `add` and 4,200 for `mul` and `div`, and finding a
bit length, about as many steps. So `mul` and `div` cost about twice `add`: at the stand-in's rate
(§7.3), about 7 ms for `add` and 14 ms for `mul` or `div`, and a few kernel steps each with `Nat` natives for powers, shifts
and bit length [inferred].

**Why this model:** order laws reduce to a few facts about one rounding function, stated in §9.
Lean's unpacked model (align exponents, then normalise per operation, §4.2) is faster to run
without natives, but every law has to see through the alignment; Flocq's real-number view needs
real numbers, which Stitchwort doesn't have [inferred]. Comparisons in the specification are of
integers: "nearer to `num / den × 2^scale`" is decided by cross-multiplying, so no rationals are
needed either.

**What std proves.** Only laws a program needs, plus the short core of §9: `add` commutative;
`sub = add ∘ neg`; `x + (-0.0) = x`; and the trigger's monotonicity `0.0 <= d → s <= s + d`. More
when a program asks (backlog only with a concrete trigger).

**Keep the `f64` code for running.** The runtimes don't change, and with D1368 (i) the evaluator
uses the `f64` code while programs and tests run.

**Test the definitions against hardware harder than today.** Beyond `float_paths.rs`'s edge set:
cases built to hit rounding boundaries (ties, results just under and over a power of two, overflow
at exactly the halfway point past `MAX_VALUE`, subnormal results, quotients with a remainder of
exactly half). Lean uses Berkeley TestFloat and UCBTest for this [read, PR #14079]; whether either
can be used here (licence, format) is open.

## 9. The central lemmas and the trigger proof

`units` forgets the sign of zero, so lemmas that go back from units to a double must carry the
sign, and addition's zero sign is not always the first argument's (`-0.0 + 0.0 = +0.0`). The lemmas
below make the sign explicit; all are about finite doubles, and the specials are §3's case table.
Here `<=` is the total order on `Float` and `≤`, `<` are on `Int`. [inferred: statements and proof
outline written for this note, not yet checked by the kernel.]

| Lemma | Statement |
|---|---|
| `unitsZero` | `x` is a zero → `units x = 0` |
| `unitsZeroIsZero` | `isFinite x`, `units x = 0` → `x` is a zero |
| `unitsPositive` | `isFinite x`, `0.0 < x` → `0 < units x` |
| `roundRatioUnits` | `isFinite x` → `roundRatio (units x) 1 (-1074) (signBit x) = x` |
| `roundRatioSignIrrelevant` | `num ≠ 0` → `roundRatio num den scale z1 = roundRatio num den scale z2` |
| `roundRatioZero` | `roundRatio 0 den scale False = 0.0` |
| `roundRatioStrictMono` | `den > 0`, `num1 < num2` → `roundRatio num1 den scale z1 <= roundRatio num2 den scale z2`, for **any** `z1`, `z2` |
| `addFinite` | `isFinite x`, `isFinite y` → `x + y = roundRatio (units x + units y) 1 (-1074) (signBit x ∧ signBit y)` |
| `zeroLeZero` | `x` is a zero → `x <= 0.0` |

`roundRatioStrictMono` holds for any zero signs because the inputs differ: if both results are
nonzero, rounding to nearest is monotone (§3); if both are zeros, the zero rule gives `num`'s sign
to a nonzero `num` and `z` only to `num = 0`, and in each case (both negative, negative and zero,
negative and positive, zero and positive, both positive) the left zero is `-0.0` or the right is
`+0.0`, so the left is `<=` the right. The non-strict form is false: `roundRatio 0 1 e False = 0.0`
is not `<=` `roundRatio 0 1 e True = -0.0`. So is the tempting `s <= roundRatio (units s) 1 (-1074) z`
for every `z` and every `s` other than `-0.0`: at `s = 0.0` with `z = True` it gives `-0.0`. The
proof therefore splits off the zero case first.

`roundRatioUnits`, `roundRatioSignIrrelevant`, `roundRatioZero` and `roundRatioStrictMono` are
proved from the rounding specification (§8.1), not from the algorithm; `addFinite` is the case
table of `add`'s definition.

**Proof of `0.0 <= d → s <= s + d`.** If `s` or `d` is not finite, §3's table. Otherwise `d` is
`0.0` or positive, since `0.0 <= d` excludes `-0.0` and negatives; so `signBit d = False` and the
zero sign in `addFinite` is `False`.

1. **`d = 0.0`.** `units d = 0` (`unitsZero`), so `s + d = roundRatio (units s) 1 (-1074) False`
   (`addFinite`).
   - If `units s ≠ 0`: this is `roundRatio (units s) 1 (-1074) (signBit s)`
     (`roundRatioSignIrrelevant`), which is `s` (`roundRatioUnits`). So `s <= s + d` by reflexivity.
   - If `units s = 0`: `s` is a zero (`unitsZeroIsZero`) and `s + d = 0.0` (`roundRatioZero`);
     `s <= 0.0` (`zeroLeZero`). This covers `s = -0.0`, where the sum is `+0.0`.
2. **`d` positive.** `0 < units d` (`unitsPositive`), so `units s < units s + units d`. Then
   `s = roundRatio (units s) 1 (-1074) (signBit s)` (`roundRatioUnits`)
   `<= roundRatio (units s + units d) 1 (-1074) False` (`roundRatioStrictMono`, the two zero signs
   differing is allowed) `= s + d` (`addFinite`).

The lemmas compose: the only step that equates a rounding with `s` uses `s`'s own sign, and the
only step across different zero signs is the strict one. The same lemmas give `x + (-0.0) = x`
for finite `x` (the zero sign is `signBit x ∧ True`, which is `signBit x`, so `addFinite` and
`roundRatioUnits` give `x` directly, zeros included), and `roundRatioStrictMono` with `den = |units y|` is what a later monotonicity law
for `div` would use.

## 10. Staging

Each stage is one lane; each ends with the named tests passing.

1. **The model's core, `add` and `sub`, and the checking mode.** `units`, `signBit`, `roundRatio`
   with its location-based core, and `roundScaled` in `Float.Model` (a sibling file of
   `std/Float/Float.sw`); `Float.add` and `Float.sub` become definitions calling the model. Float
   natives fire only while a program runs (D1368 (i)), for these two and for today's exact
   operations. Hashes and bindings updated. Tests: the gate passes; the definitions agree with Node
   on the `float_paths.rs` edge set and on rounding-boundary cases; kernel time per closed `add` in
   checking measured. Exit questions (implementation choices): opaque or transparent definitions;
   whether `Nat` natives for powers, shifts and bit length are needed now, by the measurement.
2. **The laws.** In `Float.Theory`: the rounding specification and the proof that `roundRatio`
   meets it; the lemmas of §9; then `Float.addMonotoneRight : 0.0 <= d → s <= s + d`,
   `Float.addComm`, `Float.subAddNeg`, `Float.addNegZero`. The trigger proof drops its hypothesis
   and uses the law. Unit tests stay beside the theorems.
3. **`mul`, `ofInt`, `ofNat`** through `roundScaled`; the general `toInt`/`ofInt` theorem
   (`float.md:1150-1156`).
4. **`div` through `roundRatio`; `rem`, `floor`, `ceil`, `trunc`, `round` directly over the bits.**
   `div` adds only its case table (division by zero, infinities) and the sign handling of §8.2; the
   rounding is stage 1's. Tests add quotients that land exactly on a tie and just either side of
   one. After this, no float operation has a reduction rule, and the kernel computes every one
   through its definition; DESIGN.md §13's float row is rewritten to say so (the float trust left
   is the `Nat` natives', plus `toText`, which the kernel never computes), and `FLOAT_CONTRACT`
   governs only the runtimes (§3.3 of the float note).

Stages 3 and 4 have no program waiting for them; they can wait for one, but leaving a mix of
"definition" and "primitive with rule" is a permanent two-mechanism cost, so doing them soon after
is reasonable [inferred].

## 11. Decisions

**D1363 — Should std be able to prove laws about rounding operations, and by what mechanism?**
The rounding operations have no laws today. Options:

- (a) No laws; programs carry hypotheses.
- (b) A few trusted laws, each an axiom, tested against hardware.
- (c) A model in the logic plus one axiom per primitive (Rocq).
- (d) The primitives become definitions over the bits (Lean, Isabelle; how `Nat` already works).
  **[Recommended]**: no axiom; laws provable; how the kernel computes them is D1368.

**D1364 — What does the trigger proof do until the law is proved (end of stage 2)?** Options:

- Keep the hypothesis until then; nothing is added to the trust base. **[Recommended]**
- Add `0.0 <= d → s <= s + d` now as an axiom, and delete it when stage 2 proves it.

**D1365 — The shape of the model.** Options:

- Exact, then round: every finite double as a whole number of units of 2^-1074, and one rounding
  function (`roundRatio`, with `roundScaled` its `den = 1` case) used by `add`, `sub`, `mul`, `div`,
  `ofInt` and `ofNat`. Simplest to prove order laws from; slower when computed without natives.
  **[Recommended]**
- Lean's shape: unpack to sign/mantissa/exponent, align, compute, normalise, per operation. Faster
  to compute; each law has to reason through the alignment.
- A port of Flocq's `binary_float` and proofs. Most proved results, but its proofs are about real
  numbers, which Stitchwort doesn't have.

**D1366 — Which laws std proves.** Options:

- The trigger's law and a small core (`add` commutative, `sub` is `add` of `neg`, `x + (-0.0) =
  x`, and the rounding lemmas of §9), then more only when a program needs one. **[Recommended]**
- A general library now (error bounds, Sterbenz, more): a project of its own, with no program
  asking for it.

**D1368 — May the kernel use the hardware for floats while checking proofs?** With (d), a
float operation is a definition; the question is whether the `f64` code also runs inside the
kernel, where it decides which `rfl` proofs are accepted. Options:

- (i) No: the kernel always computes floats through their definitions; the `f64` code runs only
  while a program or test runs, and in the runtimes (Lean's position). No float code can make the
  kernel prove `False`; a closed float operation inside a proof costs milliseconds.
  **[Recommended]**
- (ii) Yes, as trusted natives, like `Nat`'s, with the natives-off gate as defence in depth.
  Checking stays fast; a disagreement between the `f64` code and the definition on any input is a
  proof of `False`.
- (iii) Yes for everyday checking, plus a final check with float natives off for std, releases and
  shipped builds. Trust of (i) for what ships; costs a new switch, a cache mode, a CI job and two
  meanings of "checked".

**D1369 — Is the exact-then-round model also the executable code?** `Float` (what programs use),
`Float.Model` (executable definitions) and `Float.Theory` (specification, lemmas, laws) are separate
either way, with laws stated about `Float`'s operations. Options:

- Yes: `units` and `roundRatio` are the executable model now; a faster model can replace them later
  by proving it meets the same rounding specification, without changing any law. **[Recommended]**:
  the simplest thing that works, and the layering keeps the later change cheap.
- No: write a faster executable model now (Lean's unpacked form) and prove it equal to the
  exact-then-round specification. Faster kernel checking without natives; the bridge proof is the
  largest single piece of work, for a speed no program needs yet.

## Appendix A: scripts run

`monotone.js` and `laws.js` are in the session scratchpad (`flscripts/`), run with Node 22.23.3.
Both compare doubles in the canonical-NaN total order, computing `Float.orderKey`'s key from the
bits (`OfNat bits` with the sign clear, `-(magnitude + 1)` with it set, the NaN as
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

**The kernel-cost stand-in** (`flcost/pow100.sw` in the session scratchpad), checked with the
release `stitchwort` binary built on 26 October 2026. The file is the definitions below followed
by `theorem p1: proxy 1 = 2051 := rfl` up to `p100`; the baseline file has one trivial `rfl`
theorem over `Nat`.

```
import Std (Nat)

def bitLenFuel: Nat → Nat → Nat
  | Zero, _ => 0
  | Succ fuel, n => if n == 0 then 0 else 1 + bitLenFuel fuel (n / 2)

def proxy (k: Nat): Nat := bitLenFuel 2200 (Nat.pow 2 2046 + k) + (Nat.pow 2 2046 / Nat.pow 2 1000) % 7
```

```
$ time stitchwort check base.sw      real 0.15
$ time stitchwort check pow100.sw    real 0.87
```

A single run each, on a quiet machine; (0.87 − 0.15) / 100 ≈ 7 ms per stand-in operation. It
measures the shape of the work (a power of two of rounding size, a bit length, a division), not the
real `roundRatio`, which doesn't exist yet.

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
- Lean kernel, `type_checker.cpp` (`reduce_nat`, `whnf`, `lazy_delta_reduction`):
  https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp
- Lean `@[implemented_by]` documentation:
  https://github.com/leanprover/lean4/blob/master/src/Lean/Compiler/ImplementedByAttr.lean ;
  `@[extern]`: https://github.com/leanprover/lean4/blob/master/src/Lean/Compiler/ExternAttr.lean
- Lean reference, axioms (`native_decide` and compiler trust): https://lean-lang.org/doc/reference/latest/Axioms/
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
