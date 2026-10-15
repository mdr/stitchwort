# Proposal: native numbers

**Status:** accepted and implemented, 15 October 2026: option A, for `Nat` only (no `Int` yet). See "Numbers" in [`docs/core.md`](../core.md). One correction to the text below: extracted JS did use `bigint`, but its arithmetic still recursed once per unit. It now uses native `bigint` operations too.

## The problem

`Nat` is defined in the prelude as `Zero | Succ Nat`, and the compiler represents it that way. That keeps the kernel small and makes proofs about numbers straightforward, but it has costs that now show up regularly:

- **Depth.** A literal `n` is `n` nested constructors, and checking, evaluating, printing and dropping it all recurse once per `Succ`. Literals above about 1,000 overflow a test thread's 2 MB stack, so they're capped at 200. The browser has a similarly small stack.
- **Speed.** `add`, `mul`, `/` and `leq` recurse once per unit. `200 * 25` is 5,000 nested calls, which also overflowed the stack during testing.
- **The JS output is already fast.** Extracted code uses `bigint`, so this only affects the compiler's own evaluation (type checking, `rfl` proofs, tests, the REPL and the playground).

## Options

### A. Kernel-native literals and arithmetic (what Lean does)

The core gets a literal form, `Nat(n)` with an arbitrary-precision `n`. Conversion treats `Nat(0)` as `Zero` and `Nat(n+1)` as `Succ (Nat(n))`. Matching on a literal takes the `Zero` or `Succ` branch without building the chain.

Specific prelude definitions (`add`, `sub`, `mul`, `leq`, `divFuel`, `decEqNat`) get a **native implementation** that the evaluator uses when all their arguments are literals. Otherwise they unfold as now, so proofs by induction are unaffected.

- **Gain:** large numbers are cheap everywhere, and proofs work exactly as today.
- **Cost:** the native implementations join the trusted base. A bug in one could make the kernel accept `2 + 2 = 5`. That's the same trade-off Lean makes, where the kernel trusts GMP.
- **Mitigation:** differential tests comparing each native implementation with its unary definition on many inputs. The native operations would be listed alongside the extractor and the encoders as trusted components (DESIGN.md §13), so the trust stays visible.

### B. A binary `Nat` in the language

Define naturals by their binary digits (as Rocq's `N` and `positive` do), with arithmetic written in Stitchwort.

- **Gain:** nothing new to trust. Arithmetic is logarithmic.
- **Cost:** induction on binary numbers is awkward. Most proofs would need a conversion to and from unary first, and simple facts like `n + 0 = n` stop being one-liners. That works against "programming first".

### C. Compact unary values only

Keep everything unary in meaning, but represent a literal as a count internally, and walk `Succ` chains with loops instead of recursion.

- **Gain:** removes the depth problem for literals, with nothing new to trust.
- **Cost:** arithmetic is still one step per unit, so `1000 * 1000` is still a million steps.

## Recommendation

**A**, with the native operations limited to a short list. Each one is checked against its definition by a property test, and the list is documented as part of the trusted base.

C is a cheap first step whichever option is chosen, and would also help with other deep structures (long lists). Independently, the playground's WASM stack can be raised with a linker flag.

## Questions for you

1. Is growing the trusted base by a handful of arithmetic functions acceptable, given the tests and the visibility?
2. Should `Int` (signed, with truncating division, DESIGN.md §10) arrive at the same time, since it would share the machinery?

## As built: what a native must compute

A native replaces a definition, so it must compute exactly what the definition does, as the whole result: for numbers and booleans that's the answer, but for a native that returns a proof it's the proof term too, up to conversion. Otherwise turning natives on changes which `rfl` proofs check, even though both proofs are valid. ([compact text](compact-text.md#what-the-same-meaning-must-mean) states this obligation for any native: `expand(native_D(args)) ≡ D(expand(args))` under the reference rules.)

The first native `decEqNat` didn't meet it. The definition recursed with `decSucc`, so `decEqNat 3 5` computed a `No` holding a refutation three `succInjective` steps deep, while the native gave `No (natNeq 3 5 rfl)`; `rfl` couldn't prove a copy of the definition equal to the native on `3 5`. Building the definition's own refutation natively would make it as deep as the smaller number, which defeats a native. So the definition changed instead, to one whose result is small:

```
decEqNatFrom : (m : Nat) -> (n : Nat) -> (b : Bool) -> eqNat m n = b -> Decidable (m = n)
decEqNatFrom m n True  h = Yes (eqNatSound m n h)
decEqNatFrom m n False h = No (natNeq m n h)

decEqNat Zero     Zero     = Yes rfl
decEqNat Zero     (Succ n) = No (natNeq 0 (Succ n) rfl)
decEqNat (Succ m) Zero     = No (natNeq (Succ m) 0 rfl)
decEqNat (Succ m) (Succ n) = decEqNatFrom (Succ m) (Succ n) (eqNat m n) rfl
```

For two numbers this computes `Yes rfl` (`eqNatSound m m rfl` unfolds to `rfl`) or `No (natNeq m n rfl)` (`natNeq` needs a fourth argument, so it stays as it is), which is what the native returns. `eqNatSound` is native too, giving `rfl` when its two numbers are equal, whatever its proof argument; otherwise the `Yes` would count down. It matches on both numbers only so that it waits for them, as before: unfolding `decEqNat x 0` around an unknown `x` would copy `x` into two places in elaborated decisions and so in generated JS.

Trade-offs: `decEqNat (Succ m) (Succ n)` no longer computes to `decSucc m n (decEqNat m n)`, so a proof by induction that relied on that would need `eqNat` reasoning instead (nothing in the repository did); the prelude has two more definitions, and one more native (`eqNatSound`, as simple as `eqNatRefl`).

The tests (`crates/driver/tests/natives.rs`) compare whole results by conversion, not just which constructor came back: every native with natives on against its definition with all natives off, on all small inputs and random ones; on numbers above 2^64, against one step of its definition (a copy of its body whose recursive calls go to the native), which with the small-number comparison is an induction; and `rfl` proofs that a copy of each proof-returning definition equals the native.

| Native | Result | Agrees with its definition, as a whole result |
|---|---|---|
| `add`, `sub`, `mul`, `divFuel` | a number | yes: a number is its `Succ` chain |
| `leq`, `eqNat` | a `Bool` | yes: a constructor without fields |
| `decEqNat` | `Yes rfl` or `No (natNeq m n rfl)` | yes, since the definition changed (above) |
| `eqNatRefl` | `rfl` | yes: the definition counts down to `rfl` |
| `eqNatSound` (equal numbers only) | `rfl` | yes: the definition gives `cong Succ` of `rfl`, which is `rfl`, ignoring the proof |
| the `k + x` shortcuts (`add`, `sub`, `leq`, `eqNat`, `eqNatRefl`) | some steps of the definition at once | yes: each is a number of the definition's own steps |
