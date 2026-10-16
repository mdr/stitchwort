# Proposal: integers (`Int`)

**Status:** draft 1, 16 October 2026. Docs only: nothing here is built yet.
Waiting on the user's answers ([Questions for you](#questions-for-you)) and
an external review ([Open questions for the reviewer](#open-questions-for-the-reviewer)).

This note is meant to be read without knowing the codebase. The first section
describes the parts of Stitchwort it touches. Names are written in the style
of the [namespaces](namespaces.md) proposal, whose stage 1 (moving the
prelude into `Std` namespaces) is being built now: `Nat.add`, `Int.add`,
`Nat.decEq`, and so on. Where a name exists today under an older spelling,
both are given once.


## Decisions (16 October 2026)

The user's answers to the questions for the user:

1. `-18 % 100` is `82`: Euclidean `/` and `%` on `Int`, as recommended.
2. A minus sign works on any expression (`-x`), not only on literals
   (arguments still need brackets: `f (-5)`).
3. `x % d` on `Int` gives an `Int`; a separate `Nat`-returning version
   exists for indexing.

## Contents

- [Summary](#summary)
- [Background: the parts of Stitchwort involved](#background-the-parts-of-stitchwort-involved)
- [Goals and non-goals](#goals-and-non-goals)
- [What other systems do](#what-other-systems-do)
- [Which division?](#which-division)
- [Representation options](#representation-options)
- [Making it compact](#making-it-compact)
- [The definitions](#the-definitions)
- [Literals](#literals)
- [Operators](#operators)
- [Conversions](#conversions)
- [Number patterns on `Int`](#number-patterns-on-int)
- [Termination](#termination)
- [Proofs about integers](#proofs-about-integers)
- [The JavaScript boundary and generated code](#the-javascript-boundary-and-generated-code)
- [Hashing and binding](#hashing-and-binding)
- [Trusted code](#trusted-code)
- [Testing](#testing)
- [Staging](#staging)
- [Recommendation](#recommendation)
- [Questions for you](#questions-for-you)
- [Open questions for the reviewer](#open-questions-for-the-reviewer)
- [Documents to update if accepted](#documents-to-update-if-accepted)
- [What I couldn't verify](#what-i-couldnt-verify)
- [Sources](#sources)

## Summary

In plain terms:

- **`Int` is an ordinary data type**, defined the way Lean and Agda define
  it: an integer is either a natural number, or "minus (one more than) a
  natural number".

  ```
  type Int : Type =
    | OfNat (n : Nat)      -- 0, 1, 2, …
    | NegSucc (n : Nat)    -- -1, -2, -3, …  (NegSucc n means -(n + 1))
  ```

  Every integer has exactly one form, so `=` on `Int` behaves as expected,
  and the existing machinery (pattern matching, `==` through `auto`, hashing,
  extraction) works on it unchanged.
- **It's fast without new trusted code in the kernel.** Its fields are
  `Nat`s, which are already stored as arbitrary-precision numbers, and its
  operations are short definitions that call the `Nat` operations that
  already run natively. This is what Lean's kernel does too: it accelerates
  `Nat` and has no special support for `Int`.
- **In extracted JavaScript, an `Int` is a `bigint`**, of either sign, inside
  the generated code and at the boundary, as `Nat` is today. The `Int`
  operations get native JS implementations, each bound to the exact prelude
  definition it replaces by content hash, as the text natives are.
- **`/` and `%` on `Int` use Euclidean division**: the remainder is never
  negative. `-18 % 100` is `82`, which is what a dial or a wrapping grid
  coordinate needs. This reverses DESIGN.md §10, which chose JavaScript's
  truncating division. Truncating and flooring division are also provided,
  under their own names.
- **Literals are typed by context.** `5` is a `Nat` unless the context says
  `Int`; `-5` is always an `Int`. Arithmetic operators pick `Nat.add` or
  `Int.add` by the type of their non-literal operands, so `x + 1` works for
  either type. Nothing converts between `Nat` and `Int` silently:
  `n.toInt` (or `Nat.toInt n`) does it explicitly.

## Background: the parts of Stitchwort involved

Stitchwort is a small, strict, pure, total, dependently typed language,
written in Rust. A trusted kernel re-checks everything the elaborator
produces. Checked programs can be extracted to JavaScript.

- **`Nat`** is defined in the prelude as `Zero | Succ Nat`, and that is what
  it means. A number is *stored* as one arbitrary-precision value
  (`Value::Nat`), which behaves exactly like its chain of `Succ`s. A number
  with an unknown inside is kept as "`k` `Succ`s around `x`"
  (`Value::NatAdd`). See [native numbers](native-numbers.md).
- **Natives.** Nine prelude definitions on `Nat` (`add`, `sub`, `mul`,
  `leq`, `eqNat`, `divFuel`, `decEqNat`, `eqNatRefl`, `eqNatSound`) run
  natively in the kernel's evaluator when their arguments are numbers
  (`crates/core/src/native.rs`). Each **must compute exactly what its
  definition computes, as the whole result, proofs included**, or turning
  natives on would change which `rfl` proofs check
  ([native numbers, as built](native-numbers.md#as-built-what-a-native-must-compute);
  stated generally as `expand(native_D(args)) ≡ D(expand(args))` in
  [compact text](compact-text.md#the-obligation-for-a-native)). They're
  part of the trusted base (DESIGN.md §13), and tested against their
  definitions.
- **Binding.** Built-in syntax (`+`, literals, `==`, …) is bound to fixed
  prelude declarations by identity, through a registry
  (`crates/core/src/registry.rs`, [namespaces §4.7](namespaces.md#47-operators-and-other-built-in-syntax)).
  Whether a native may *replace* a definition is decided separately: by an
  exact type check for the number natives, and by content hash for compact
  text and the JS text natives ([compact text](compact-text.md#binding-natives-to-the-definitions-they-replace)).
- **Number patterns** (`f 404 = …`) compile to a kernel *number switch*,
  `NumCase(n, [(k₁, b₁), …], default)`, rather than `Succ` chains
  ([number patterns](number-patterns.md)). A catch-all after number
  patterns learns nothing about the value.
- **Division** on `Nat` takes an implicit proof that the divisor isn't zero,
  `[auto ok : d != 0]`, which the compiler finds for literal divisors.
  `Nat` subtraction stops at zero (`3 - 5 = 0`).
- **`auto` and `==`.** `a == b` is `toBool d` for a decision procedure `d`
  for `a = b`, found by type: any definition returning `Decidable (a = b)`.
- **Termination** is structural: a recursive call must pass something
  matched out of a parameter.
- **Extraction.** `Nat` is a JS `bigint` inside generated code and at the
  boundary; decoding refuses anything that isn't a non-negative `bigint`.
- **Content hashes** identify each checked declaration (DESIGN.md §11).
- **There is no `Int` yet.** DESIGN.md §10 plans one, with division
  truncating toward zero to match JS `BigInt`; §12 lists it as a planned
  boundary type (`bigint`).

## Goals and non-goals

**Goals**

1. **Signed integers for programs**: differences, coordinates, offsets,
   parsing `-12` from input, arithmetic modulo `n` with negative values.
   The motivating uses are Advent of Code 2025 and library code exported to
   JavaScript.
2. **Signed integers for proofs**: `=` means equality of values, and simple
   facts (`Int.neg (Int.neg x) = x`, the division law) are provable without
   heroics.
3. **As fast as `Nat`, within a constant factor**, in the checker,
   the REPL, tests and generated JS: no unary representation anywhere.
4. **A small, visible trusted base**, in the same style as `Nat`'s.
5. **Clean JS**: an `Int` is a `bigint` of either sign at the boundary.

**Non-goals (for now)**

- **Fixed-width integers** (`Int64`, `U32`). DESIGN.md §10 plans them
  separately, as a `Nat` or `Int` in a range with explicitly wrapping
  operations.
- **Implicit conversions** between `Nat` and `Int` (Lean inserts them;
  see [Operators](#operators)). They can be added later without breaking
  programs.
- **A decision procedure for arithmetic** (Lean's `omega`, Rocq's `lia`).
  Valuable, but a project of its own ([Proofs](#proofs-about-integers)).
- **Type classes** or user-extensible operators. Operators work on a fixed
  set of types.
- **Rationals, floats.**

## What other systems do

| System | Integer type | Representation for proofs | How it's made fast | `/` and `%` |
|---|---|---|---|---|
| **Lean 4** | `Int` | `ofNat : Nat → Int` and `negSucc : Nat → Int` [L1, L2] | Runtime: small integers unboxed, large ones GMP [L1]. Kernel: **no** `Int`-specific reduction; it accelerates `Nat` operations (`add`, `sub`, `mul`, `div`, `mod`, `gcd`, `beq`, `ble`, bitwise ops, `pow`) [L3], and `Int` computes by unfolding to them | Euclidean (`Int.ediv`, `Int.emod`); also `tdiv`/`tmod` (truncating), `fdiv`/`fmod` (floor), `bdiv`/`bmod` (balanced). Division by zero is defined to be zero [L1, L4] |
| **Agda** | `ℤ` (bound with `BUILTIN INTEGER`) | `pos : Nat → Int` and `negsuc : Nat → Int` [A1] | "Unlike for natural numbers, there is no special representation of integers at compile-time" [A1]: the data type over built-in naturals is fast enough. The standard library defines subtraction "using `_<ᵇ_` and `_∸_` rather than inductively so that it is backed by builtin operations" [A2] | Euclidean: the remainder is a natural number below `∣ d ∣` [A3] |
| **Idris 2** | `Integer`, a primitive | Opaque primitive; `Nat` is compiled to `Integer` at runtime [I1] | Primitive | Not checked for this note |
| **Rocq** | `Z` | `Z0 | Zpos positive | Zneg positive`, with `positive` in binary (`xI`, `xO`, `xH`) [R1] | Binary representation: logarithmic without trusted code. Separately, primitive 63-bit integers, "regular axioms" that "must be trusted" [R2] | `Z.div`/`Z.modulo` floor; Euclidean in `ZDivEucl` ("convention 'E'" of Boute) [R3] |
| **F\*** | `int` | "unbounded, primitive mathematical integers"; `nat = x:int{x >= 0}` is a refinement [F1] | Primitive; facts are proved by an SMT solver [F1] | Not checked for this note |
| **SMT-LIB** | `Int` | (a logic, not a language) | — | Boute's Euclidean definition: `m = n·q + r`, `0 ≤ r ≤ |n| − 1` [S1] |
| **Haskell** | `Integer` | — | GMP | `div`/`mod` floor, `quot`/`rem` truncate [H1] |
| **Python** | `int` | — | — | floor: "The modulo operator always yields a result with the same sign as its second operand (or zero)" [P1] |
| **JavaScript `BigInt`** | `bigint` | — | — | truncate: `/` "truncated towards zero", `%` "always takes the sign of the dividend"; `RangeError` on `0n` [J1, J2] |

**Literals.** Lean has no separate integer literals: a numeral `n` means
`OfNat.ofNat n` for whatever type is expected, with a default instance making
it `Nat` when nothing else is known, and `-5` is prefix negation applied to
the literal `5` [L5]. Haskell similarly defaults an ambiguous numeric type to
`Integer` (`default (Integer, Double)`) [H2]. Lean's arithmetic operators go
through an elaborator (`binop%`) that looks at the whole tree of operators,
"tries to solve for a type that each of the operands in the expression tree
can be coerced to, while taking into account the expected type", and inserts
coercions at the leaves, so `n + i` with `n : Nat` and `i : Int` works [L6].

**Arithmetic decision procedures.** Lean's `omega` resolves "integer and
natural linear arithmetic problems" (with `Nat` cast to `Int`, and `/`, `%`
by constants) [L7]; Rocq's `lia` "solves linear goals over `Z`", supporting
`nat` by translating to `Z` [R4]. Both treat the integers, not the naturals,
as the home of arithmetic reasoning.

**What this tells us.** The two proof assistants closest to Stitchwort's
design (inductive types, a small kernel, natives for `Nat`) both define the
integers as a two-constructor data type over `Nat`, and both rely on `Nat`'s
acceleration rather than adding integer primitives. The systems with
primitive integers (Idris 2, F\*, Rocq's `PrimInt63`) either keep them away
from proofs, trust axioms, or lean on an external solver.

## Which division?

Integer division has several conventions. They all satisfy `a = d·q + r` with
`|r| < |d|`; they differ in which `q` they pick when `d` doesn't divide `a`
[B1, D1]:

- **T (truncate):** round the quotient toward zero. The remainder has the
  sign of the dividend. C99, Rust's `/`, JS `BigInt`, Haskell's `quot`/`rem`.
- **F (floor):** round toward negative infinity. The remainder has the sign
  of the divisor. Python, Haskell's `div`/`mod`, Knuth.
- **E (Euclidean):** the remainder is always `0 ≤ r < |d|`. Boute 1992,
  SMT-LIB, Lean's `/` and `%`, Agda's standard library.

Leijen's comparison table [D1]:

| `a`, `d` | T: `q`, `r` | F: `q`, `r` | E: `q`, `r` |
|---|---|---|---|
| 8, 3 | 2, 2 | 2, 2 | 2, 2 |
| 8, -3 | -2, 2 | -3, -1 | -2, 2 |
| -8, 3 | -2, -2 | -3, 1 | -3, 1 |
| -8, -3 | 2, -2 | 2, -2 | 3, 1 |
| -1, 2 | 0, -1 | -1, 1 | -1, 1 |

**F and E agree whenever the divisor is positive**, which is nearly always.
They differ only for negative divisors. **T is the odd one out** for a
negative dividend, which is the common case in practice.

**The example that matters.** Advent of Code 2025's first puzzle has a safe
dial numbered 0 to 99, starting at 50, turned by instructions such as `L68`
(68 clicks toward lower numbers) and `R48`; "turning the dial left from 0 one
click makes it point at 99" [AoC1]. With integers:

```
type Turn =
  | Left (clicks : Nat)
  | Right (clicks : Nat)

turn : Int -> Turn -> Int
turn pos (Left n)  = (pos - n.toInt) % 100
turn pos (Right n) = (pos + n.toInt) % 100
```

`turn 50 (Left 68)` is `-18 % 100`. Euclidean (and floor) division gives
`82`, the right answer. Truncating division, as DESIGN.md §10 currently
specifies, gives `-18`, a position that doesn't exist on the dial, and
every program like this needs a correction, `((x % d) + d) % d`, which is
what MDN recommends for JS [J2]. Today, with only `Nat`, the same function
needs `(pos + 100 - n % 100) % 100`, which is correct but makes the reader
check that it can't go below zero.

**Recommendation: Euclidean (E) for `Int`'s `/` and `%`**, because:

- The remainder is always a valid index (`0 ≤ x % d < |d|`) whatever the
  signs, which is what wrapping, bucketing and grid code needs.
- It's the choice of SMT-LIB, Lean and Agda, so their lemma statements and
  any future solver integration line up; Lean's own reason was that it's
  "consistent with the conventions used in SMT-LIB, and Mathlib" and that
  "often mathematical reasoning is easier with these conventions" [L4].
  Boute argues it's the most regular of the definitions; Leijen summarises
  him as showing that "despite its widespread use, truncated division is
  shown to be inferior to the other definitions" [D1].
- On natural numbers it agrees with `Nat`'s `/` and `%`, so
  `n.toInt / d.toInt = (n / d).toInt` (a lemma to prove, not a definitional
  equality; see [Proofs](#proofs-about-integers)).
- It costs one comparison and one addition in JS over the native operators
  (Leijen's "algorithm E" [D1]; see [JS](#the-javascript-boundary-and-generated-code)).

E rather than F because its remainder is non-negative even for a negative
divisor; the two only differ there, and a non-negative remainder is the
simpler invariant to state and use. Truncating (`Int.tdiv`, `Int.tmod`) and
flooring (`Int.fdiv`, `Int.fmod`) division are provided under those names,
for porting code that relies on them.

**Division by zero stays a type error**, as for `Nat`: `/` and `%` take
`[auto ok : d != 0]`. Lean defines `x / 0 = 0` instead [L1]; Stitchwort has
already chosen proofs, and `auto` finds `100 != 0` for a literal divisor (at
`Int`, through `Int.decEq`).

**What `%` returns.** Lean's `Int.emod` returns an `Int`; Agda's `_%_`
returns a natural number [A3], which makes the "never negative" fact part of
the type. This note recommends an `Int`, so `a = d * (a / d) + a % d` is an
equation in one type, plus `Int.modNat : Int -> (d : Nat) -> [auto ok : d != 0] -> Nat`
for indexing (`(pos - 1).modNat 100`). [Question 3](#questions-for-you).

## Representation options

The *definition* of `Int` decides what proofs see, what `=` means, and how
much case analysis lemmas need. Speed is a separate question
([Making it compact](#making-it-compact)): every option below can be made
fast.

### A. `OfNat Nat | NegSucc Nat` (Lean, Agda) — recommended

```
type Int : Type =
  | OfNat (n : Nat)
  | NegSucc (n : Nat)    -- means -(n + 1)
```

- **One form per integer.** `0` is `OfNat 0` and nothing else, so equality of
  values is equality of constructors and fields: decidable equality is a
  two-line case split, and `=` needs no extensionality lemma.
- **No proof fields**, so no proof-irrelevance questions (compare `Char`,
  which needed `Char.ext` because `MkChar` carries a proof).
- **The embedding of `Nat` is a constructor.** `n.toInt` is `OfNat n`, which
  is injective and disjoint from `NegSucc` for free, and computes on unknown
  `n`. So `OfNat a + OfNat b` computes to `OfNat (a + b)` by definition, for
  any `a` and `b`. This matters because most integers in programs start as
  natural numbers (lengths, parsed digits, counts).
- **Cost:** the negative side is shifted by one, so negation needs a case on
  zero (`Int.neg (OfNat 0) = OfNat 0`, `Int.neg (OfNat (Succ n)) = NegSucc n`,
  `Int.neg (NegSucc n) = OfNat (Succ n)`), and lemmas about addition go
  through a helper that subtracts two naturals (`Int.subNatNat`). Lean's and
  Agda's libraries show it's workable at scale.

### B. Sign-magnitude with a separate zero: `Zero | Pos Nat | Neg Nat`

Rocq's `Z` has this shape (with binary positives) [R1]. With unary `Nat`,
`Pos n` would mean `n + 1` and `Neg n` would mean `-(n + 1)`.

- **Symmetric:** negation swaps `Pos` and `Neg`, with no case on zero.
- **But the embedding of `Nat` isn't a constructor:** `ofNat 0 = Zero` and
  `ofNat (Succ n) = Pos n`, so `ofNat x` is stuck while `x` is unknown, and
  `ofNat a + ofNat b = ofNat (a + b)` becomes a lemma proved by cases instead
  of a computation. Every literal and every conversion is off by one, in both
  signs.
- One more constructor in every case split.

A is better where it matters most (code that converts `Nat` to `Int`); B is
better for negation. Lean and Agda both chose A.

### C. A sign and a magnitude: `MkInt (negative : Bool) (magnitude : Nat)`

The simplest-looking option, and **wrong without a side condition**: `+0` and
`-0` are different values, so `MkInt False 0 = MkInt True 0` is false, and
`==`, `rfl` and hashing all distinguish them. Adding a proof field
(`negative = True -> magnitude != 0`) makes the form unique again, but then
every operation must build that proof, equality needs an extensionality lemma
(as `Char` does), and the kernel does more work per operation. Rejected.

### D. A quotient of pairs: `(a, b)` meaning `a - b`

The textbook construction (a pair of naturals, with `(a, b) ~ (c, d)` when
`a + d = b + c`). Stitchwort has no quotient types, so `(3, 1)` and `(2, 0)`
would be different values: `=` would be the wrong equality, and `auto`, `==`,
hashing and the JS codec would all see the representation. Normalising pairs
(one side zero) brings back C's proof-field problem. Rejected.

### E. Binary (Rocq's `Z` over `positive`)

Logarithmic arithmetic with nothing new to trust. Rejected for the reason
[native numbers](native-numbers.md#b-a-binary-nat-in-the-language) rejected a
binary `Nat`: induction on binary numbers is awkward, and Stitchwort already
has fast unary-meaning `Nat`, which A builds on.

### F. A primitive, opaque type (Idris 2's `Integer`, F\*'s `int`)

A kernel type with built-in operations and no constructors. Proofs would need
axioms for its laws (as Rocq's primitive integers are "regular axioms" [R2]),
or an external solver (F\*). That goes against "proofs about programs" with a
small trusted base. Rejected.

**Recommendation: A.**

## Making it compact

With A, an `Int` value in the kernel is `OfNat` or `NegSucc` around a
`Value::Nat`, so it's already compact: `-10^30` is one constructor around one
big number. The question is whether `Int`'s *operations* need natives.

### K1. No `Int` natives in the kernel — recommended

`Int`'s operations are ordinary prelude definitions, each a case split on its
arguments' constructors followed by one or two calls to `Nat` operations that
already run natively ([The definitions](#the-definitions)). This is exactly
how Lean's kernel handles `Int`: its kernel reduces `Nat.add`, `Nat.sub`,
`Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.beq`, `Nat.ble` and a few more with
big-number arithmetic, and there is no `Int`-specific reduction [L3]. Agda's
standard library does the same deliberately [A2].

- **Kernel trusted code added: none.** `Int` is an ordinary data type and its
  operations are ordinary definitions that the kernel checks. The whole-result
  obligation holds trivially: there's no native standing in for an `Int`
  definition, so the definition *is* what runs.
- **Cost per operation:** a few evaluation steps (one or two case splits, a
  constructor) around one `Nat` native, instead of one native step.
  Unmeasured (see [What I couldn't verify](#what-i-couldnt-verify)); expected
  to be a small constant factor, since arithmetic on large numbers is
  dominated by the big-number work itself, which is the same.
- **What stays stuck on unknowns** follows the definitions, with no special
  rules to get wrong. `OfNat a + OfNat b` computes to `OfNat (a + b)` for any
  `a`, `b`. `x + 1` with unknown `x : Int` is stuck (the definition must know
  `x`'s constructor). `OfNat x + NegSucc 2` is stuck on `x` (subtracting
  `3` needs to know whether `x ≥ 3`). These match what a reader would expect
  from the definitions, and what Lean's kernel does.

### K2. A compact `Value::Int` with kernel natives

A `Term::Int`/`Value::Int` holding a signed big number, meaning its expansion
(`OfNat n` or `NegSucc n`), and natives for `Int.add`, `Int.mul`, `Int.ediv`,
… under the whole-result obligation, as for `Nat`.

- **Gain:** saves the case steps and a constructor allocation per operation.
- **Cost:** a new term and value form, so the full audit that compact text
  needed (matching, conversion, quotation, hashing, termination, unification,
  printing, both evaluators, JS); a new list of trusted natives; and care
  with proof-returning natives (`Int.decEq`'s `No`), where `Nat.decEq` was
  the precedent for getting it wrong
  ([auditing `decEqNat`](compact-text.md#auditing-deceqnat)).

**Recommendation: K1**, with K2 only if measurements later show `Int`
arithmetic dominating real checking or test time. K1 costs nothing to undo:
K2 could be added later behind the same definitions, bound to them by content
hash, without changing any program's meaning.

## The definitions

A sketch of the prelude's `Std.Int`, following Lean's definitions [L2, L4]
adapted to Stitchwort. Exact names are suggestions; how a namespace's
declarations are written is [namespaces §4.3](namespaces.md#43-declaring-into-a-namespace).

```
type Int : Type =
  | OfNat (n : Nat)
  | NegSucc (n : Nat)

-- `n.toInt`
Nat.toInt : Nat -> Int
Nat.toInt n = Int.OfNat n

-- `-x`
Int.neg : Int -> Int
Int.neg (OfNat Zero)     = OfNat Zero
Int.neg (OfNat (Succ n)) = NegSucc n
Int.neg (NegSucc n)      = OfNat (Succ n)

-- `m - n` for naturals, as an integer. One native subtraction decides
-- which side is bigger (Lean's `subNatNat`).
Int.subNatNat : Nat -> Nat -> Int
Int.subNatNat m n = Int.subNatNatFrom m n (n - m)

Int.subNatNatFrom : Nat -> Nat -> Nat -> Int
Int.subNatNatFrom m n Zero     = OfNat (m - n)   -- n ≤ m
Int.subNatNatFrom m n (Succ k) = NegSucc k       -- n - m = k + 1

Int.add : Int -> Int -> Int
Int.add (OfNat m)   (OfNat n)   = OfNat (m + n)
Int.add (OfNat m)   (NegSucc n) = Int.subNatNat m (Succ n)
Int.add (NegSucc m) (OfNat n)   = Int.subNatNat n (Succ m)
Int.add (NegSucc m) (NegSucc n) = NegSucc (Succ (m + n))

Int.sub : Int -> Int -> Int
Int.sub a b = Int.add a (Int.neg b)

Int.mul : Int -> Int -> Int    -- by signs, on the magnitudes: `natAbs a * natAbs b`
Int.leq : Int -> Int -> Bool   -- by constructors, then `Nat.leq`
Int.LessEq, Int.LessThan : Int -> Int -> Prop   -- behind `<=` and `<`
Int.decEq : (a : Int) -> (b : Int) -> Decidable (a = b)   -- behind `==`, by `Nat.decEq`
Int.compare : Int -> Int -> Ordering

Int.div : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> Int   -- Euclidean, behind `/`
Int.mod : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> Int   -- Euclidean, behind `%`
Int.tdiv, Int.tmod, Int.fdiv, Int.fmod   -- truncating and flooring, same types
Int.modNat : Int -> (d : Nat) -> [auto ok : d != 0] -> Nat

Int.natAbs : Int -> Nat         -- |x| as a Nat
Int.abs    : Int -> Int
Int.toNat  : Int -> Nat         -- negatives become 0 (Lean's `Int.toNat`)
Int.toNatChecked : Int -> Maybe Nat
Int.sign   : Int -> Int         -- -1, 0 or 1
Int.toText : Int -> Text        -- "-42"
Text.toInt : Text -> Maybe Int  -- "-42", "17"; same rules as `Text.toNat`, with an optional `-`
```

`Int.div` and `Int.mod` follow Lean's case split for `ediv` and `emod` [L4]:
on non-negative `a` and positive `d` they are `Nat`'s `/` and `%` on the
magnitudes; for a negative `a = NegSucc m` and positive `d`, the quotient is
`NegSucc (m / d)` and the remainder `d - 1 - m % d`; a negative divisor
negates the quotient and leaves the remainder unchanged. Each case calls
`Nat`'s division with a divisor of the form `Succ _`, for which `auto` proves
`!= 0`.

**Decisions must stay small.** `Int.decEq` should compute `Yes rfl` or a
constant-size `No`, never a proof as deep as a number. Written as "match the
constructors, then use `Nat.decEq` on the fields and wrap it", it does: the
`Yes` case is `Yes (Eq.cong OfNat rfl)`, which computes to `Yes rfl`, and the
`No` case wraps the `Nat.decEq` refutation (constant size since the
`decEqNat` fix) in one function. The same "whole result" test the `Nat`
natives have applies, in spirit: `rfl` on `Int.decEq 3 5` against a copy of
its definition (which is trivially true under K1, and becomes a real test
under K2).

## Literals

Today a numeral always means a `Nat` (`crates/elab/src/check.rs`, the
`Expr::Num` case infers type `Nat`). With two number types there are three
options:

1. **Explicit conversions only:** `5` is always a `Nat`; write `(5).toInt`
   or `Nat.toInt 5`, and `Int.neg (Nat.toInt 5)` for `-5`. Nothing new, but
   arithmetic on integers becomes noisy (`x + Nat.toInt 1`).
2. **A suffix**, such as `5i`. Short, but unusual, and still noisy in
   patterns and data.
3. **Type-directed literals** (recommended): a numeral takes the type the
   context expects, as in Lean (through `OfNat`) and Haskell (through
   `fromInteger`) [L5, H2], but with a fixed set of types instead of a type
   class.

The rules for option 3, all in the elaborator (the kernel only ever sees
`Term::Nat` for a `Nat` and constructor applications such as
`OfNat (Term::Nat 5)` for an `Int`):

- **Checking `k` against `Nat`** gives the number, as today. **Against
  `Int`** it gives `OfNat k`.
- **A negative literal `-k`** (a `-` directly before a numeral, where an
  operand starts) gives `NegSucc (k - 1)`, or `OfNat 0` for `-0`. Checked
  against `Nat` it's an error, with a note: "a `Nat` can't be negative; use
  an `Int`". When nothing is expected, it's an `Int`, the only type it can
  have.
- **When nothing says which**, a non-negative literal is a `Nat`, exactly as
  today, so no existing program changes meaning. Lean has the same default
  [L5]. If the expected type is an unsolved metavariable, the literal is also
  a `Nat` (today's behaviour); waiting for the metavariable to be solved, as
  Lean does, would be friendlier but is more machinery (reviewer question
  R3).
- **Against any other type**, the existing type-mismatch error, mentioning
  that numerals can be `Nat` or `Int`.

**A trap to document.** `let d = 3 - 5` with no type anywhere is a `Nat`
subtraction, so `d` is `0`. That's today's behaviour, and DESIGN.md §10
already documents that `Nat` subtraction stops at zero; the fix is to say
which type is meant, `let d : Int = 3 - 5`. Nothing reports this, since it
isn't an error; a warning for "a subtraction of literals that stops at zero"
would be cheap to add later.

**Unary minus on other expressions.** `-x` for an `Int` expression `x` means
`Int.neg x`, under the same "where an operand starts" rule as negative
literals. As in Haskell, an argument needs parentheses: `f (-5)`,
`f (-x)`; `f -5` is `f - 5`. Whether to have general `-x` or only negative
literals (with `x.neg` otherwise) is [question 2](#questions-for-you).

## Operators

**Today** every arithmetic and comparison operator is bound to one `Nat`
definition through the registry: `+` is always `Nat.add`, `<` always
`Nat.LessThan`, and so on. `++` is the one exception, choosing `Text.append`
or `List.append` by its left operand's type. `==` and `!=` already work on
any type with a decision procedure, so they need nothing new for `Int`
beyond `Int.decEq` existing.

**Proposed:** the operators `+ - * / %` and `< <=` have one registry entry
**per number type**, `Nat` and `Int`, and choose between them by the type of
the operands:

1. Treat a maximal tree of these operators as one unit, as Lean's `binop%`
   does [L6]. For `0 + 1 + n`, the leaves are `0`, `1` and `n`.
2. If the whole tree has a known expected type (for `+ - * / %`), that's the
   operand type. Otherwise infer the first leaf that isn't a literal (or
   negated literal) and use its type. If every leaf is a literal: `Int` if
   any is negative, otherwise `Nat`.
3. The type's head must be `Nat` or `Int`; anything else is an error listing
   the types the operator works on (today's error for `+` on a non-`Nat`).
4. Check every leaf against that type. Literals take it (as above); a leaf of
   the other number type is an error with a hint: "`n` is a `Nat`; write
   `n.toInt`".
5. Bind each operator to that type's registry entry (`Int.add`,
   `Int.LessThan`, …), by identity, never by looking up a name in scope.

So `x + 1`, `1 + x`, `0 - x`, `x * -2` and `pos % 100` work for `x : Int`,
and every existing `Nat` program elaborates exactly as before (all its
leaves are `Nat`s or literals, which default to `Nat`).

**No implicit conversions.** `n + i` with `n : Nat` and `i : Int` is an
error with a hint, where Lean would insert `↑n` [L6]. Explicit conversions
are easier to read in proofs, and adding coercions later only turns errors
into programs.

**How this relates to namespaces.** Namespaces' reviewer question R6 asks
whether "an operator means `T.op` for the head `T` of its left operand's
type" is the right direction, given numeric literals that default to `Nat`
([namespaces §8](namespaces.md#8-extending-it-later-without-breaking-anything)).
This note answers the literal half: it must be **the first non-literal
leaf**, not the left operand, or `0 + x` would commit to `Nat` from the `0`.
It doesn't open operators to user types: the table is closed (`Nat`, `Int`),
like `++`'s. Generalising to `T.add` for any `T` later is compatible: it only
turns "`+` doesn't work on `T`" errors into programs.

**Subtraction means different things on the two types:** `3 - 5` is `0` on
`Nat` and `-2` on `Int`. That's already documented for `Nat`, and the
operator follows the operands' type, so the meaning is fixed by the types a
reader can see.

## Conversions

| Function | Meaning | Notes |
|---|---|---|
| `Nat.toInt n` / `n.toInt` | `OfNat n` | A constructor, so free in JS and transparent in proofs |
| `Int.toNat x` | `x` if `x ≥ 0`, else `0` | Lean's name and behaviour; mirrors `Nat` subtraction's clamping |
| `Int.toNatChecked x` | `Just n` or `Nothing` | For when a negative value is a bug |
| `Int.natAbs x` | `|x|` as a `Nat` | The natural measure for recursion (see [Termination](#termination)) |
| `Int.abs x` | `|x|` as an `Int` | |
| `Int.sign x` | `-1`, `0` or `1` | |
| `Int.toText`, `Text.toInt` | decimal text | `Text.toInt` is what AoC parsing needs |

A `Nat` that comes from a proof-carrying context (a length, an index) stays a
`Nat`; code converts at the point where signs appear.

## Number patterns on `Int`

```
describe : Int -> Text
describe 0    = "zero"
describe (-1) = "minus one"
describe 404  = "not found"
describe _    = "something else"
```

**No kernel change.** An `Int` number pattern is the corresponding
constructor pattern around a `Nat` number pattern: `404` is `OfNat 404`, and
`-1` is `NegSucc 0`. The existing pattern compiler then produces an ordinary
`case` on `Int` with a `NumCase` in each branch:

```
case x of
  OfNat m   -> NumCase(m, [(0, "zero"), (404, "not found")], "something else")
  NegSucc k -> NumCase(k, [(0, "minus one")], "something else")
```

A side with no number patterns is just its default rows, with no `NumCase`
(the kernel refuses an empty table, and the compiler already never makes
one).

The number-patterns policy carries over unchanged: a number pattern tests
for a value; `OfNat`/`NegSucc` patterns expose structure; a catch-all after
number patterns learns nothing about the value. `f (OfNat n)` and
`f (NegSucc n)` remain the way to split on sign with information.

In generated JS, the `case` on `Int` is a sign test on the `bigint`, and each
`NumCase` a `switch` (see below). A later optimisation could switch on the
`bigint` directly (`case -1n:`), which the language doesn't promise either
way.

## Termination

`Int` isn't recursive: its constructors hold `Nat`s, not `Int`s. So there is
no structural recursion *on an `Int`* beyond one level; a function that
recurses does so on a `Nat` it gets from the `Int`:

```
-- the sum 0 + 1 + … + n, or 0 + -1 + … + n for negative n,
-- where `Nat.triangle` is the same sum on naturals, recursing on its `Nat`
Int.triangle : Int -> Int
Int.triangle (OfNat n)   = (Nat.triangle n).toInt
Int.triangle (NegSucc k) = Int.neg (Nat.triangle (Succ k)).toInt
```

or with `Int.natAbs x` as fuel or a measure. Lean offers induction
principles for `Int` that step through negatives; Stitchwort can add one as an
ordinary theorem later if proofs need it. The termination checker needs no
change.

## Proofs about integers

**What works immediately:** `rfl` on closed values (`3 - 5 = -2`,
`-18 % 100 = 82`), because the definitions compute on numbers through the
`Nat` natives; `==` and `if h : a = b` through `Int.decEq`; `auto` for
literal side conditions such as `100 != 0`.

**What needs a library:** algebraic laws (commutativity and associativity of
`Int.add`, distributivity, `Int.neg (Int.neg x) = x`, the division law
`a = d * (a / d) + a % d` with `0 <= a % d < |d|`, `n.toInt / d.toInt = (n /
d).toInt`). With representation A, these are case splits on constructors
plus lemmas about `Nat` and `Int.subNatNat`; Lean's and Agda's libraries are
the template. **Stitchwort's `Nat` lemma library is thin today**: the prelude
has injectivity and disequality lemmas but not `Nat.add` commutativity or any
division law. So a useful `Int` library starts with a `Nat` one. This is the
main cost of integers, and it's the same with every representation.

**Not proposed:** a decision procedure for linear arithmetic (`omega`,
`lia`). Both work over the integers, with naturals cast in [L7, R4], so
having `Int` is a prerequisite if Stitchwort ever wants one.

## The JavaScript boundary and generated code

**Representation.** An `Int` is a `bigint` of either sign everywhere in
generated code, as `Nat` is a non-negative `bigint`:

| Stitchwort | Generated JS |
|---|---|
| `OfNat n` | `n` |
| `NegSucc n` | `-n - 1n` |
| matching `x` on `Int` | `if (x >= 0n) { const n = x; … } else { const n = -x - 1n; … }` |
| `n.toInt` | `n` (no code) |

This is a bijection between `Int` values and `bigint`s, so the boundary
encoding is lossless and needs no tag. It's the same kind of special case as
`Nat`'s (a registry-identified data type compiled to a primitive), in the
trusted extractor.

**Boundary.** `.d.ts` type `bigint`. Decoding is strict, like `Nat`'s and
`Text`'s: anything that isn't a `bigint` (including a `number` such as `5`,
and a numeric string) is refused with `StitchwortInputError` ("expected a
bigint"). Encoding can't fail.

**Natives.** Each `Int` operation gets a native JS implementation, used only
for the exact definition it was written for (content hash, as the text
natives are), and otherwise the definition is compiled as written. For
example:

```js
// Int.add, Int.mul, Int.neg: the operators directly
(a) => (b) => a + b
// Int.mod (Euclidean), Leijen's algorithm E on BigInt's truncating %
(a) => (d) => { const r = a % d; return r < 0n ? (d > 0n ? r + d : r - d) : r; }
// Int.div (Euclidean)
(a) => (d) => { const q = a / d, r = a % d; return r < 0n ? (d > 0n ? q - 1n : q + 1n) : q; }
// Int.tdiv, Int.tmod: BigInt's / and % directly
```

`Int.decEq` returns `{ tag: a === b ? "Yes" : "No" }` (proofs are erased).
The proof arguments (`ok : d != 0`) are erased, so a native never sees a zero
divisor from checked code; it can't throw `RangeError`.

A wrong JS native gives a wrong answer in JS, not a false theorem
(DESIGN.md §13's "native text in extracted JS" row is the precedent).

## Hashing and binding

- **No new hashing rules.** `Int` is a data type; `-5` elaborates to the term
  `NegSucc 4`, which is hashed like any constructor application around a
  number. Two spellings of the same value (`-5` and `NegSucc 4`) give the
  same term, so the same hash.
- **Syntax** (literals at `Int`, the `Int` operator entries) binds to `Std.Int`
  declarations through the registry, by identity, so a user's own `Int` or
  `add` changes nothing (namespaces stage 0's invariants).
- **JS natives and the `bigint` representation** are bound by content hash
  to the declarations they were written for (`Int` itself, which pins its
  constructors and field types, and each operation), with the policy of the
  JS text natives: a mismatch means the definition is compiled as written,
  and a test fails printing the new hashes, so a deliberate prelude change
  forces someone to re-check the natives.
- **Kernel:** nothing to bind under K1. Under K2, the same content-hash
  binding as compact text, before any `Int` native may fire.

## Trusted code

| Component | Change | Trusted? |
|---|---|---|
| Kernel (checking, evaluation, conversion, hashing) | **None** under K1 | — |
| Kernel natives | None under K1; the existing `Nat` natives are exercised more | Already trusted |
| Prelude `Std.Int` definitions | New, ordinary definitions | No: checked by the kernel. Their *meaning* is the specification, as for `Nat` |
| Elaborator: literals at `Int`, negative literals, unary minus, operator choice, `Int` patterns | New | No: the kernel re-checks the output |
| Registry entries for `Int` | New | No more than today's (identity only) |
| Extractor: `Int` as `bigint`, its matching and constructors, boundary codec | New | Yes, like `Nat`'s (DESIGN.md §12–§13: the extractor and codecs are trusted) |
| JS natives for `Int` operations | New, about ten one-liners | Yes, in JS only: a bug is a wrong JS answer, not a false theorem |
| Printer (`-5` rather than `NegSucc 4`) | New | No |

So the kernel's trusted base doesn't grow, which is the main argument for
K1. The extractor's does, by about as much as `Nat` added.

## Testing

- **Definitions against a reference.** Every `Int` operation, evaluated by
  the kernel's evaluator, against Rust's `num_bigint::BigInt` (with the
  Euclidean and floor variants computed independently in the test), on all
  pairs in `-20..20`, Leijen's table, values around `±2^64` and random large
  values, with natives on and off.
- **JS natives against their definitions**, compiled without natives, under
  Node, on the same inputs: the existing differential-extraction tests,
  extended.
- **Boundary:** negative and positive `bigint`s round-trip; `5`, `"5"`,
  `5.0`, `null` refused.
- **Elaboration:** `x + 1`, `1 + x`, `0 - x`, `-x`, `f (-5)`, `-5` against
  `Nat` (error), `n + i` (error with hint), `3 - 5` inferred (a `Nat`, `0`),
  `let d : Int = 3 - 5` (`-2`), chains of literals, and every existing
  example unchanged (snapshot tests).
- **Patterns:** the `describe` example in both evaluators and in JS, a
  column mixing `0`, `-1` and `OfNat n` patterns, the catch-all regression.
- **Must reject** (DESIGN.md §13 style, each paired with an accepted
  neighbour): `x / 0` at `Int`; `bad : (x : Int) -> x % 3 = OfNat 1` by
  `rfl`; `-1 : Nat`; `Int.neg x = x` by `rfl` for unknown `x`.
- **Example programs:** the dial, and a grid walk with negative coordinates.

## Staging

Integers come after namespaces stage 1 (they go in `Std.Int`, and the
registry needs per-type operator entries). Dot notation (namespaces stage 2)
makes `n.toInt` read well, but isn't required: `Nat.toInt n` works without
it.

1. **Stage 1: the type and its operations.** `Std.Int` with the definitions
   above (Euclidean `/` and `%`, the truncating and flooring variants,
   conversions, `Int.toText`, `Text.toInt`); type-directed and negative
   literals; unary minus; operators chosen by operand type; `Int` number
   patterns; printing; JS representation, boundary codec and natives; the
   tests above; DESIGN.md updated.
2. **Stage 2: lemmas.** A `Nat` lemma library (commutativity, associativity,
   the division law) and the `Int` one on top. Driven by what the Advent of
   Code proofs actually need.
3. **Measure.** If `Int` arithmetic shows up in profiles of checking or
   tests, consider K2 then, with its own note.
4. **Later, separately:** fixed-width types, implicit `Nat` → `Int`
   coercions, operators for user types, a linear-arithmetic decision
   procedure.

## Recommendation

- **Representation A** (`OfNat Nat | NegSucc Nat`), as in Lean and Agda.
- **K1**: no `Int` natives or new value forms in the kernel; `Int`'s
  operations are ordinary definitions over the existing `Nat` natives.
- **Euclidean `/` and `%`** for `Int` (reversing DESIGN.md §10's truncating
  choice), with `Int.tdiv`/`Int.tmod` and `Int.fdiv`/`Int.fmod` by name;
  division by zero stays a type error.
- **Type-directed literals** with `Nat` as the default, negative literals
  that are always `Int`, and unary minus.
- **Operators** choose `Nat` or `Int` by the first non-literal leaf of the
  operator tree (or the expected type); no implicit conversions.
- **`bigint`** for `Int` in generated JS and at the boundary, with JS natives
  bound by content hash.

## Questions for you

1. **Division with negative numbers.** Should `-18 % 100` be `82` (Euclidean,
   as Lean, Agda and SMT solvers do; the remainder is never negative), rather
   than `-18` (as JavaScript and Rust's `%` do, and as DESIGN.md §10 says
   today)? The JS-style versions would still exist as `Int.tdiv`/`Int.tmod`.
   Recommended: yes, Euclidean.
2. **Minus sign.** Should `-x` work on any integer expression, or only on
   numbers written in the source (`-5`), with `x.neg` for everything else?
   Either way, an argument needs brackets: `f (-5)`. Recommended: allow
   `-x` generally.
3. **What `%` returns.** Should `x % 100` on integers give an `Int` (Lean),
   or a `Nat` (Agda), since it's never negative? An `Int` keeps arithmetic in
   one type; a `Nat` can be used directly as a list index. Recommended: an
   `Int`, plus `x.modNat 100` giving a `Nat`.

## Open questions for the reviewer

- **R1. Representation.** Is A's advantage (the `Nat` embedding is a
  constructor, so `OfNat a + OfNat b` computes to `OfNat (a + b)` on open
  terms) worth its asymmetric negation, compared with
  `Zero | Pos Nat | Neg Nat`? Are there proof-ergonomics costs of A that
  Lean's and Agda's experience shows and this note misses?
- **R2. No kernel natives (K1).** Is there any way that defining `Int`'s
  operations over the existing `Nat` natives could expose a whole-result
  discrepancy that the `Nat` natives' tests don't already cover (for
  example, `Nat.sub` or `Nat.decEq` being called on open terms in new
  shapes from `Int.subNatNat`)? Is "K2 only on measured need" the right
  stance?
- **R3. Literals.** Is "default to `Nat` when the expected type is unknown
  or an unsolved metavariable" acceptable, or should literals be postponed
  until the metavariable is solved (Lean's approach)? What breaks if a
  literal commits to `Nat` too early inside `Just 5 : Maybe ?a`, given that
  today every literal is a `Nat` anyway?
- **R4. Operators.** Is choosing the operand type from "the expected type,
  else the first non-literal leaf of the operator tree" sound and
  predictable enough? Should comparison operators (`<`, which yields a
  `Prop`) and `==` (which uses `auto`) follow exactly the same leaf rule? This
  also answers namespaces' R6 in part: is a closed per-type table the right
  first step before `T.op`?
- **R5. Division.** E rather than F: the two differ only for negative
  divisors. Is the non-negative remainder worth disagreeing with Haskell and
  Python there? And `%` returning `Int` versus `Nat` (question 3).
- **R6. Number patterns.** Is compiling an `Int` pattern to a constructor
  `case` with a `NumCase` per side complete, including mixed columns
  (`0`, `-1`, `OfNat n`, `_`) and multiple columns, given the existing
  rules for when a column is split by constructors?
- **R7. Extraction.** Is mapping `NegSucc n` to `-n - 1n` and matching by
  sign test the right place for this special case (the extractor, trusted),
  rather than compiling `Int` as a tagged object and optimising later?
- **R8. Proof support.** For a language aiming at "proofs about programs",
  how soon does the lack of a linear-arithmetic procedure become the
  bottleneck once `Int` exists?

## Documents to update if accepted

- **DESIGN.md §10:** `Int` division becomes Euclidean, with the truncating
  and flooring variants named; drop "matches JS `BigInt` so extracted code
  can use the native operators directly".
- **DESIGN.md §12:** `Int` moves from planned to supported in the boundary
  table; the note "`Int` division and remainder are defined to match
  `BigInt`'s" changes.
- **DESIGN.md §13:** the native-arithmetic row mentions that `Int` has no
  kernel natives; the extracted-JS natives row gains the `Int` natives.
- **docs/syntax.md:** literals, negative literals, unary minus, operators on
  `Nat` and `Int`.
- **docs/core.md "Numbers":** `Int` as a data type over `Nat`.

## What I couldn't verify

- **No measurements.** I didn't build or run anything (other agents were
  building). The claim that K1 costs only a small constant factor per
  operation is an estimate from the definitions' shape, not measured.
- **Boute's paper itself** wasn't read: its content is cited through
  Leijen's note [D1], SMT-LIB [S1] and the Rocq documentation [R3], which
  agree on what it defines. The DOI comes from SMT-LIB's citation and wasn't
  checked against the ACM library.
- **Lean's `omega`:** the official docstring wasn't retrieved; the
  description comes from the frontend source's own doc comment ("for
  resolving integer and natural linear arithmetic problems") and a summary of
  that file [L7].
- **Lean's kernel list of accelerated `Nat` operations** comes from the
  kernel source [L3]; the reference manual marks fewer of them as kernel
  overrides (it doesn't mention `Nat.div` and `Nat.mod` there). I relied on
  the source.
- **Agda's division convention** is inferred from the types and lemmas in
  `Data.Integer.DivMod` (the remainder is a natural number below `∣ d ∣`)
  [A3], not from a stated definition.
- **Idris 2's and F\*'s division semantics** weren't checked, and neither was
  how proofs about Idris 2's primitive `Integer` work in practice.
- **Rocq's default `Z.div`** is described as floor from the comment in
  `ZDivEucl` [R3], not from `Z.div`'s own documentation.
- **Advent of Code 2025 day 1, part 2** wasn't read (it isn't visible
  without solving part 1); only part 1's dial is used here.
- **The elaborator details** (how `++` currently chooses by type, how
  `auto` would find `Int.decEq` for `d != 0`) were read from the namespaces
  note and the code's structure, not exercised.

## Sources

- **[L1]** Lean Language Reference, *Integers*: "Integers are represented
  either as a natural number or as the negation of the successor of a natural
  number"; the runtime "stores “small” signed numbers directly, while larger
  numbers use a fast arbitrary-precision arithmetic library (usually GMP)";
  "The `Div Int` and `Mod Int` instances implement Euclidean division";
  "division by `0` is defined to be `0`".
  <https://lean-lang.org/doc/reference/latest/Basic-Types/Integers/>
- **[L2]** Lean 4 source, `src/Init/Data/Int/Basic.lean`: `inductive Int`
  with `ofNat` and `negSucc`; `Int.neg`, `Int.subNatNat`, `Int.add`;
  `@[extern "lean_int_add"]` etc. for compiled code.
  <https://github.com/leanprover/lean4/blob/master/src/Init/Data/Int/Basic.lean>
- **[L3]** Lean 4 source, `src/kernel/type_checker.cpp`, `reduce_nat`:
  kernel reduction of `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`,
  `Nat.gcd`, `Nat.beq`, `Nat.ble`, `Nat.land`, `Nat.lor`, `Nat.xor`,
  `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.pow`; no `Int`-specific reduction.
  Also the reference manual, *Natural Numbers*: "if these primitives did not
  correspond to their definitions as Lean functions, it could undermine
  soundness".
  <https://github.com/leanprover/lean4/blob/master/src/kernel/type_checker.cpp>,
  <https://lean-lang.org/doc/reference/latest/Basic-Types/Natural-Numbers/>
- **[L4]** Lean 4 source, `src/Init/Data/Int/DivMod/Basic.lean`: the E, F and
  T conventions; "we decided it was better to use `ediv` and `emod` for the
  default typeclass instances", "consistent with the conventions used in
  SMT-LIB, and Mathlib", "often mathematical reasoning is easier with these
  conventions"; the case definitions of `Int.ediv` and `Int.emod`.
  <https://github.com/leanprover/lean4/blob/master/src/Init/Data/Int/DivMod/Basic.lean>
- **[L5]** Lean Language Reference, *Numeric Literals*: a literal is
  `OfNat.ofNat n`; "A default instance of `OfNat Nat n` ensures that the type
  `Nat` can be inferred when no other type information is present"; "There
  are no separate integer literals. Terms such as `-5` consist of a prefix
  negation" applied to a natural number literal.
  <https://lean-lang.org/doc/reference/latest/Terms/Numeric-Literals/>
- **[L6]** Lean 4 source, `src/Lean/Elab/Extra.lean`, the `binop%`
  elaborator: "tries to solve for a type that each of the operands in the
  expression tree can be coerced to, while taking into account the expected
  type for the entire expression tree"; coercions inserted at the leaves.
  <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Extra.lean>
- **[L7]** Lean 4 source, `src/Lean/Elab/Tactic/Omega/Frontend.lean`: "The
  `omega` tactic, for resolving integer and natural linear arithmetic
  problems."
  <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Omega/Frontend.lean>
- **[A1]** Agda manual, *Built-ins*: `data Int : Set where pos : Nat → Int;
  negsuc : Nat → Int` with `BUILTIN INTEGER`, `INTEGERPOS`,
  `INTEGERNEGSUC`; "Unlike for natural numbers, there is no special
  representation of integers at compile-time since the overhead of using the
  data type compared to Haskell integers is not that big"; natural-number
  built-ins (`NATPLUS`, `NATMINUS`, `NATTIMES`, `NATEQUALS`, `NATLESS`,
  `NATDIVSUCAUX`, `NATMODSUCAUX`): "The primitive implementation is used to
  evaluate applications to closed terms, and the Agda definition is used
  otherwise."
  <https://agda.readthedocs.io/en/latest/language/built-ins.html>
- **[A2]** Agda standard library, `Data.Integer.Base`: `+_` and `-[1+_]`;
  `_⊖_` defined "using `_<ᵇ_` and `_∸_` rather than inductively so that it is
  backed by builtin operations".
  <https://agda.github.io/agda-stdlib/master/Data.Integer.Base.html>
- **[A3]** Agda standard library, `Data.Integer.DivMod`: `n%d<d : n % d ℕ.<
  ∣ d ∣` (the remainder is a natural number), `a≡a%n+[a/n]*n`.
  <https://agda.github.io/agda-stdlib/master/Data.Integer.DivMod.html>
- **[I1]** Idris 2 documentation, *Builtins*: `Nat` "At runtime, Idris2 will
  automatically represent this the same as the `Integer` type."
  <https://idris2.readthedocs.io/en/latest/reference/builtins.html>
- **[R1]** Rocq Corelib, `Corelib.Numbers.BinNums`: `positive` (`xI`, `xO`,
  `xH`), `N`, and `Z` (`Z0`, `Zpos`, `Zneg`): "An integer is either zero or a
  strictly positive number (coded as a positive)".
  <https://rocq-prover.org/doc/master/corelib/Corelib.Numbers.BinNums.html>
- **[R2]** Rocq reference manual, *Primitive objects*: 63-bit machine
  integers; "These primitive declarations are regular axioms. As such, they
  must be trusted".
  <https://rocq-prover.org/doc/master/refman/language/core/primitive.html>
- **[R3]** Rocq standard library, `Numbers.Integer.Abstract.ZDivEucl`: "The
  outcome of the modulo function is hence always positive. This corresponds
  to convention 'E'" in Boute's paper; the default signature's division
  follows "the Floor convention".
  <https://rocq-prover.org/doc/v9.0/stdlib/Stdlib.Numbers.Integer.Abstract.ZDivEucl.html>
- **[R4]** Rocq reference manual, *Micromega*: "`lia` is a decision procedure
  for linear integer arithmetic"; it "provides support for `Z`, `nat`,
  `positive` and `N` by pre-processing via the `zify` tactic".
  <https://rocq-prover.org/doc/master/refman/addendum/micromega.html>
- **[F1]** *Proof-Oriented Programming in F\**, part 1: "The type `int`
  represents unbounded, primitive mathematical integers"; `let nat =
  x:int{x >= 0}`; facts proved by an SMT solver by default.
  <https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html>
- **[S1]** SMT-LIB, theory `Ints`: "div and mod according to Boute's
  Euclidean definition", with `0 ≤ r ≤ |n| − 1`.
  <https://smt-lib.org/theories-Ints.shtml>
- **[H1]** Haskell 2010 Report, §6.4.2: "`quot` is integer division truncated
  toward zero, while the result of `div` is truncated toward negative
  infinity", with the laws `(x quot y)*y + (x rem y) == x` and
  `(x div y)*y + (x mod y) == x`.
  <https://www.haskell.org/onlinereport/haskell2010/haskellch6.html>
- **[H2]** Haskell 2010 Report, §4.3.4: without a default declaration, a
  module behaves as if it had `default (Integer, Double)`.
  <https://www.haskell.org/onlinereport/haskell2010/haskellch4.html>
- **[P1]** Python language reference, *Binary arithmetic operations*: floor
  division; `%` "always yields a result with the same sign as its second
  operand (or zero)"; `x == (x//y)*y + (x%y)`.
  <https://docs.python.org/3/reference/expressions.html>
- **[J1]** MDN, *Division (/)*: "For BigInt division, the result is the
  quotient of the two operands truncated towards zero"; `RangeError` for
  `0n`.
  <https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Division>
- **[J2]** MDN, *Remainder (%)*: "It always takes the sign of the dividend";
  "To obtain a modulo in JavaScript, in place of `n % d`, use
  `((n % d) + d) % d`"; `RangeError` for a `0n` divisor.
  <https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Operators/Remainder>
- **[B1]** R. T. Boute, *The Euclidean Definition of the Functions div and
  mod*, ACM TOPLAS 14(2), April 1992, pp. 127–144, doi:10.1145/128861.128862
  (cited via [D1], [S1], [R3]; not read directly).
- **[D1]** D. Leijen, *Division and Modulus for Computer Scientists*, 2001:
  the T, F and E definitions, the comparison table reproduced above,
  "algorithm E" for Euclidean division from truncating division, and the
  summary of Boute: "Despite its widespread use, truncated division is shown
  to be inferior to the other definitions."
  <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/divmodnote.pdf>
- **[AoC1]** Advent of Code 2025, day 1, *Secret Entrance* (part 1): a dial
  0–99 starting at 50, rotations such as `L68`, "turning the dial left from 0
  one click makes it point at 99".
  <https://adventofcode.com/2025/day/1>
- This repository: [native-numbers.md](native-numbers.md),
  [number-patterns.md](number-patterns.md),
  [compact-text.md](compact-text.md) (the native obligation and binding by
  content hash), [namespaces.md](namespaces.md) (§4.7, §6, §8, R6),
  DESIGN.md §10, §12, §13, `crates/core/src/native.rs`,
  `crates/core/src/registry.rs`, the prelude's `Nat` section
  (`crates/elab/src/prelude.sw`).
