# Proposal: native numbers

**Status:** for discussion, 15 October 2026. Nothing here is implemented.

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
