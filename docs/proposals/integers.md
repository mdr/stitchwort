# Proposal: integers (`Int`)

**Status:** draft 2, 16 October 2026. Docs only: nothing here is built yet.
The user has answered the questions for the user ([Decisions](#decisions-16-october-2026)),
and an external reviewer has answered the questions for the reviewer
([Review outcome](#review-outcome)). Draft 2 adopts the review
([Changes since draft 1](#changes-since-draft-1)) and adds an
[implementation plan](#implementation-plan). Nothing is waiting on anyone
except the implementation itself, which comes after namespaces stage 1.

This note is meant to be read without knowing the codebase. The first section
describes the parts of Stitchwort it touches. Names are written in the style
of the [namespaces](namespaces.md) proposal, whose stage 1 (moving the
prelude into `Std` namespaces) is being built now: `Nat.add`, `Int.add`,
`Nat.decEq`, and so on. Where a name exists today under an older spelling,
both are given once. Inside code sketches, `OfNat` and `NegSucc` are written
unqualified for brevity; in user code they're `Int.OfNat` and `Int.NegSucc`
(see [Hashing and binding](#hashing-and-binding)).

## Decisions (16 October 2026)

The user's answers to the questions for the user:

1. `-18 % 100` is `82`: Euclidean `/` and `%` on `Int`, as recommended.
2. A minus sign works on any expression (`-x`), not only on literals
   (arguments still need brackets: `f (-5)`).
3. `x % d` on `Int` gives an `Int`; a separate `Nat`-returning version
   (`Int.modNat`) exists for indexing.

## Review outcome

The external review (16 October 2026) approved the design's shape and asked
for the elaboration rules to be made explicit before implementation. In
short:

- **R1, representation A:** approved. "One form per integer" is about
  values, not about equal *expressions* being definitionally equal
  (`Int.neg (Int.neg x) = x` for unknown `x` is still a theorem).
- **R2, K1 (no kernel natives):** approved, with new tests: the `Int`
  definitions drive the `Nat` natives through new shapes, and the existing
  tests are evidence, not a proof that every shape is right
  ([Testing the definitions](#testing-the-definitions-r2)).
- **R3, literal defaulting:** acceptable, with a documented limitation
  (`chooseFirst 5 i`), and with known expected types propagated before
  anything defaults ([Literals](#literals)).
- **R4, operators:** revise. "The first non-literal leaf" fails when that
  leaf's type is itself unknown (`List.map (\x -> x + 1) [1, 2]`), and
  equality and comparisons need the same coordinated typing
  ([Numeric expressions](#numeric-expressions)).
- **R5, division:** approved; the reviewer tested the JS formulas on 49,742
  pairs. Make the impossible zero branch explicit, check zero divisors at the
  JS boundary, and connect `%` to `Int.modNat` by a theorem
  ([Division by zero](#division-by-zero)).
- **R6, patterns:** approved; the default-branch wording was too strong
  ([Number patterns on `Int`](#number-patterns-on-int)).
- **R7, extraction:** approved, with the representation and operation
  fallbacks separated, tests through ordinary user code, and an exact
  `Text.toInt` grammar ([JS](#the-javascript-boundary-and-generated-code)).
- **R8, proofs:** no solver; bring a small lemma set forward, alongside the
  implementation ([Proofs](#proofs-about-integers)).

**Where this draft goes beyond the review.** One refinement, no
disagreements. The review's operator rule says "collect the available
numeric-type constraints before defaulting". Draft 2 makes that concrete as
two passes: leaves that contain no numeric literal are elaborated first,
since elaborating them can't default anything; leaves with literals come
after, checked against the type if it's known by then. This makes
`(if c then 1 else 2) + i` work for `i : Int`, and `Just 5 == m` for
`m : Maybe Int`, where a single left-to-right pass would commit the `1` or
the `5` to `Nat` first ([The rule](#the-rule)). It doesn't help a
polymorphic call such as `f 5 + i`, which stays under the review's
`chooseFirst` limitation. Two clarifications of the review's test list: the
"metavariable" cases are elaborator tests, since the kernel never sees
metavariables (`Globals::metas` is "empty whenever the kernel runs",
`crates/core/src/globals.rs`); and the copied-definition test for
`Int.decEq` is dropped in favour of the native-off comparison the review
asks for.

## Changes since draft 1

- **Status.** A and K1 are approved; nothing in the kernel changes.
- **Literals** ([Literals](#literals)): an expected type is reduced
  (aliases unfolded) before deciding; `Int` is recognised by registry
  identity, so a user's own type named `Int` gets no literals; known
  expected types are propagated before defaulting (`Just 5 : Maybe Int`,
  `[1, 2, 3] : List Int`); the `chooseFirst 5 i` limitation is documented
  and tested. Negative literals fold zero specially (`-0` is `OfNat 0`).
- **Operators, equality and comparisons** ([Numeric expressions](#numeric-expressions)):
  the "first non-literal leaf" rule is replaced. Arithmetic, `=`, `!=`,
  `==`, `<` and `<=` all collect constraints across their operands; an
  unknown type no longer blocks the `Nat` default; a known unsupported type
  is an error; conflicting concrete types are an error naming what decided
  each. `==` stays generic. Comparisons constrain their operands, never
  their result.
- **Unary minus** has a stated precedence (tighter than `*`, looser than
  application and `.`), checks its operand against `Int`
  (`-(3 - 5) = 2`), and nothing reaches back through a `let`
  ([Syntax](#syntax-and-precedence)).
- **Evaluation order** is left to right as written, whatever order the
  elaborator examines operands in, including effectful operands
  ([Effects and evaluation order](#effects-and-evaluation-order)).
- **Division:** the zero branch is written out (`absurd (ok rfl)`); the JS
  boundary rejects a zero divisor before any native runs; local evidence
  `h : d != 0` works; a theorem connects `%` and `Int.modNat`
  ([Division by zero](#division-by-zero)).
- **`Int.decEq`**: the whole-result test is now a native-off comparison of
  the complete `Yes`/`No` value, not a comparison with a copy of the
  definition.
- **Patterns:** the default-branch wording is corrected (the outer split
  does reveal the sign), with the reviewer's `zeroOrOther` and `pick`
  tests, and tests for repeated literals, `0` versus `-0`, `OfNat (-1)`,
  large negative keys and catch-alls before literals.
- **Extraction:** the bijection is stated; an operation's hash mismatch
  disables that native only, while an `Int` datatype mismatch disables the
  `bigint` representation and its codec together; tests go through
  ordinary user code; `Text.toInt` has an exact grammar.
- **Proofs:** a lemma checkpoint alongside implementation (double negation,
  constructor facts, `Nat.toInt` and addition, round trips; then the
  division law and remainder bounds). Still no solver.
- **Testing** is reorganised by area, with the reviewer's R2 tests split
  into small exhaustive native-off tests and large comparisons with an
  independent implementation.
- **New:** [Implementation plan](#implementation-plan), staged, marking
  which parts need careful design thinking and which are mechanical.
- **Removed:** the questions sections are replaced by the decisions and the
  review outcome above; the reviewer's questions are kept, answered, at the
  end ([The reviewer's questions](#the-reviewers-questions-answered)).

## Contents

- [Summary](#summary)
- [Background: the parts of Stitchwort involved](#background-the-parts-of-stitchwort-involved)
- [Goals and non-goals](#goals-and-non-goals)
- [What other systems do](#what-other-systems-do)
- [Which division?](#which-division)
- [Representation options](#representation-options)
- [Making it compact](#making-it-compact)
- [The definitions](#the-definitions)
- [Syntax and precedence](#syntax-and-precedence)
- [Literals](#literals)
- [Numeric expressions](#numeric-expressions)
- [Conversions](#conversions)
- [Number patterns on `Int`](#number-patterns-on-int)
- [Termination](#termination)
- [Proofs about integers](#proofs-about-integers)
- [The JavaScript boundary and generated code](#the-javascript-boundary-and-generated-code)
- [Hashing and binding](#hashing-and-binding)
- [Trusted code](#trusted-code)
- [Testing](#testing)
- [Implementation plan](#implementation-plan)
- [Recommendation](#recommendation)
- [The reviewer's questions, answered](#the-reviewers-questions-answered)
- [Documents to update](#documents-to-update)
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

  Every integer value has exactly one form, so `=` on `Int` behaves as
  expected, and the existing machinery (pattern matching, `==` through
  `auto`, hashing, extraction) works on it unchanged.
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
- **Literals are typed by context.** `5` is a `Nat` unless something says
  `Int`; `-5` and `-x` are always `Int`. An arithmetic expression, or both
  sides of a comparison, gets one number type, decided by whatever in it is
  known (the expected type, an operand's type, a minus sign), and `Nat` only
  if nothing decides. So `x + 1`, `0 == x` and `3 - 5 = -2` work for
  `x : Int`, and every existing program keeps its meaning. Nothing converts
  between `Nat` and `Int` silently: `n.toInt` (or `Nat.toInt n`) does it
  explicitly.

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
  definitions, including with every native off
  (`crates/driver/tests/natives.rs`, `crates/driver/tests/compact_text.rs`).
- **Binding.** Built-in syntax (`+`, literals, `==`, …) is bound to fixed
  prelude declarations by identity, through a registry
  (`crates/core/src/registry.rs`, [namespaces §4.7](namespaces.md#47-operators-and-other-built-in-syntax)).
  Whether a native may *replace* a definition is decided separately: by an
  exact type check for the number natives, and by content hash for compact
  text and the JS text natives ([compact text](compact-text.md#binding-natives-to-the-definitions-they-replace)).
- **How numbers and operators elaborate today** (`crates/elab/src/check.rs`):
  - A numeral `Expr::Num` always *infers* `Nat`. Checking it against an
    expected type goes through the generic fallback: infer `Nat`, then
    unify with the expected type.
  - `+ - * / % < <=` each apply one fixed `Nat` definition from the
    registry (`Builtin::Add`, `Builtin::LessThan`, …) to the two operands
    as ordinary arguments, with `/` and `%` then inserting their `auto`
    argument.
  - `=` (`equation`) infers the left side and checks the right side against
    its type; only if the left side can't be inferred at all
    (`E-CANNOT-INFER`, as for a lambda) does it infer the right side and
    check the left. `!=` is `Not (a = b)`. `==` builds the same equation
    and asks `auto` for a decision procedure.
  - `++` chooses `Text.append` or `List.append` by the type of whichever
    side can be inferred, with the same fallback as `=`.
  - In effectful code, the operands of an operator that perform operations
    run first, left to right, each bound to a fresh variable; the operator
    is then elaborated on those variables (`comp_compound` in
    `crates/elab/src/effects.rs`).
  - **`auto` obligations are the one thing postponed:** they're proved
    after the whole declaration is elaborated, first from a hypothesis in
    scope (the `h` in `if h : d != 0 then n / d else 0`), then from
    decision procedures (`crates/elab/src/auto.rs`).
- **Precedence today** (`crates/syntax/src/parser.rs`), tightest first:
  atoms with `.field` access; application; `* / %`; `+ -`; `++`; then
  `= != == < <=` (not associative). There is no prefix minus: `-` is only
  binary, and `--` starts a comment.
- **Number patterns** (`f 404 = …`) compile to a kernel *number switch*,
  `NumCase(n, [(k₁, b₁), …], default)`, rather than `Succ` chains
  ([number patterns](number-patterns.md)). A catch-all after number
  patterns learns nothing about the value.
- **Division** on `Nat` takes an implicit proof that the divisor isn't zero,
  `[auto ok : d != 0]`, which the compiler finds for literal divisors. The
  proof is in scope by name in the definition's equations (the prelude's
  `get` uses `absurd (falseNotTrue ok)` this way). `Nat` subtraction stops
  at zero (`3 - 5 = 0`).
- **`auto` and `==`.** `a == b` is `toBool d` for a decision procedure `d`
  for `a = b`, found by type: any definition returning `Decidable (a = b)`.
- **Exports check proof arguments at runtime.** Each erased proof argument
  of an exported function gets a *validator*, a decision procedure found by
  `auto` (`add_validators` in `crates/elab/src/lib.rs`), which the JS
  wrapper runs before calling the compiled code (DESIGN.md §12, "decidable
  preconditions").
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
6. **Predictable typing of numbers**: an arithmetic expression's type
   doesn't depend on which operand the elaborator happens to look at first.

**Non-goals (for now)**

- **Fixed-width integers** (`Int64`, `U32`). DESIGN.md §10 plans them
  separately, as a `Nat` or `Int` in a range with explicitly wrapping
  operations.
- **Implicit conversions** between `Nat` and `Int` (Lean inserts them;
  see [Numeric expressions](#numeric-expressions)). They can be added later
  without breaking programs.
- **Postponed literals**: a literal waiting until an unsolved type is
  solved, as Lean's are. The limitation this leaves is documented
  ([Literals](#literals)).
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
This note's rule is the same idea (one type for the whole tree, decided from
all of it) without the coercions.

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
what MDN recommends for JS [J2].

**Decided: Euclidean (E) for `Int`'s `/` and `%`** (decision 1), because:

- The remainder is always a valid index (`0 ≤ x % d < |d|`) whatever the
  signs, which is what wrapping, bucketing and grid code needs.
- It's the choice of SMT-LIB, Lean and Agda, so their lemma statements and
  any future solver integration line up; Lean's own reason was that it's
  "consistent with the conventions used in SMT-LIB, and Mathlib" and that
  "often mathematical reasoning is easier with these conventions" [L4].
- On natural numbers it agrees with `Nat`'s `/` and `%`, so
  `n.toInt / d.toInt = (n / d).toInt` (a lemma, see
  [Proofs](#proofs-about-integers)).
- It costs one comparison and one addition in JS over the native operators
  (Leijen's "algorithm E" [D1]). The reviewer checked the two JS formulas
  below on 49,742 pairs under Node 22.16.0, including all pairs in
  `-100..100` and values around `±2^64`, `±2^128` and `±2^256`: every pair
  satisfied `a = d * q + r` and `0 <= r < |d|`.

E rather than F because its remainder is non-negative even for a negative
divisor. Truncating (`Int.tdiv`, `Int.tmod`) and flooring (`Int.fdiv`,
`Int.fmod`) division are provided under those names, for porting code that
relies on them.

**What `%` returns** (decision 3): an `Int`, so `a = d * (a / d) + a % d`
is an equation in one type, plus
`Int.modNat : Int -> (d : Nat) -> [auto ok : d != 0] -> Nat` for indexing
(`(pos - 1).modNat 100`), connected to `%` by a theorem
([Division by zero](#division-by-zero), [Proofs](#proofs-about-integers)).

### Division by zero

**Division by zero stays a type error**, as for `Nat`: `/`, `%` and their
variants take `[auto ok : d != 0]`. Lean defines `x / 0 = 0` instead [L1];
Stitchwort has already chosen proofs, and `auto` finds `100 != 0` for a
literal divisor (at `Int`, through `Int.decEq`). Four requirements make it
hold everywhere:

1. **The impossible branch is written out.** A definition by cases on the
   divisor still has to cover `OfNat Zero`; the coverage checker doesn't
   know that `ok` rules it out. That equation eliminates the contradiction
   explicitly, as the prelude's `get` does for an empty list:

   ```
   Int.div a (OfNat Zero) = absurd (ok rfl)   -- ok : Not (OfNat 0 = OfNat 0)
   ```

   It's never silently omitted, and no default value is invented for it.
2. **Local evidence works.** In `if h : d != 0 then a / d else 0`, the
   obligation `d != 0` is proved by the hypothesis `h` (`auto`'s first
   rule), at `Int` exactly as at `Nat`. A test covers it, in the kernel and
   in JS.
3. **The JS boundary rejects a zero divisor before any native runs.** An
   exported function with `[auto ok : d != 0]` for `d : Int` gets a
   validator (`Int.decEq`-based, found by `auto` as for `Nat` today), and
   the generated wrapper runs it before calling the compiled code. So
   `safeDiv 7n 0n` from JS throws `StitchwortInputError` ("precondition
   `d != 0` doesn't hold"), never a `RangeError` from `BigInt`. Proof
   erasure alone wouldn't enforce anything on host inputs; the validator
   does. Inside generated code, a native can only be reached with a divisor
   for which a proof was checked, so it never sees `0n`.
4. **`%` and `Int.modNat` are connected by a theorem**, not just by
   testing: `(x.modNat d).toInt = x % d.toInt` (stated in
   [Proofs](#proofs-about-integers)). No extra runtime representation is
   needed.

## Representation options

The *definition* of `Int` decides what proofs see, what `=` means, and how
much case analysis lemmas need. Speed is a separate question
([Making it compact](#making-it-compact)): every option below can be made
fast.

### A. `OfNat Nat | NegSucc Nat` (Lean, Agda) — approved

```
type Int : Type =
  | OfNat (n : Nat)
  | NegSucc (n : Nat)    -- means -(n + 1)
```

- **One form per integer value.** `0` is `OfNat 0` and nothing else, so
  equality of values is equality of constructors and fields: decidable
  equality is a two-line case split, and `=` needs no extensionality lemma.
  (As the reviewer points out, this is about canonical *values*. Two equal
  *expressions* with unknowns in them aren't thereby definitionally equal:
  `Int.neg (Int.neg x) = x` for unknown `x` is a theorem, not `rfl`.)
- **No proof fields**, so no proof-irrelevance questions (compare `Char`,
  which needed `Char.ext` because `MkChar` carries a proof).
- **The embedding of `Nat` is a constructor.** `n.toInt` is `OfNat n`, which
  is injective and disjoint from `NegSucc` for free, and computes on unknown
  `n`. So `OfNat a + OfNat b` computes to `OfNat (a + b)` by definition, for
  any `a` and `b`. This matters because most integers in programs start as
  natural numbers (lengths, parsed digits, counts).
- **Cost:** the negative side is shifted by one, so negation needs a case on
  zero, and lemmas about addition go through a helper that subtracts two
  naturals (`Int.subNatNat`). Lean's and Agda's libraries show it's
  workable at scale.

### B. Sign-magnitude with a separate zero: `Zero | Pos Nat | Neg Nat`

Rocq's `Z` has this shape (with binary positives) [R1]. Symmetric under
negation, but the embedding of `Nat` isn't a constructor (`ofNat x` is stuck
while `x` is unknown, so `ofNat a + ofNat b = ofNat (a + b)` becomes a lemma),
and there's one more constructor in every case split. Not chosen.

### C. A sign and a magnitude: `MkInt (negative : Bool) (magnitude : Nat)`

`+0` and `-0` are different values, so `=`, `==` and hashing distinguish
them; a proof field to rule that out brings back `Char`'s extensionality
problem. Rejected.

### D. A quotient of pairs: `(a, b)` meaning `a - b`

Stitchwort has no quotient types, so `(3, 1)` and `(2, 0)` would be
different values. Rejected.

### E. Binary (Rocq's `Z` over `positive`)

Rejected for the reason [native numbers](native-numbers.md#b-a-binary-nat-in-the-language)
rejected a binary `Nat`.

### F. A primitive, opaque type (Idris 2's `Integer`, F\*'s `int`)

Proofs would need axioms for its laws [R2] or an external solver. Rejected.

## Making it compact

With A, an `Int` value in the kernel is `OfNat` or `NegSucc` around a
`Value::Nat`, so it's already compact: `-10^30` is one constructor around one
big number. The question is whether `Int`'s *operations* need natives.

### K1. No `Int` natives in the kernel — approved

`Int`'s operations are ordinary prelude definitions, each a case split on its
arguments' constructors followed by one or two calls to `Nat` operations that
already run natively ([The definitions](#the-definitions)). This is exactly
how Lean's kernel handles `Int` [L3]; Agda's standard library does the same
deliberately [A2].

- **Kernel trusted code added: none.** `Int` is an ordinary data type and its
  operations are ordinary definitions that the kernel checks. There's no
  native standing in for an `Int` definition, so the definition *is* what
  runs.
- **Why it can't introduce a new mismatch, and why it still needs tests.**
  If every `Nat` native agrees with its definition on every input, then an
  `Int` definition built from them computes the same thing with natives on
  or off. But "agrees on every input" is what the `Nat` natives' tests give
  evidence for, not a proof, and `Int`'s definitions call them in shapes
  those tests may not have reached: `Nat.sub` with the larger argument
  second, `Nat.decEq` under a constructor, arguments that are partly known
  (`n + 5` with `n` unknown). [Testing the definitions](#testing-the-definitions-r2)
  covers those shapes.
- **Cost per operation:** a few evaluation steps (one or two case splits, a
  constructor) around one `Nat` native. Unmeasured; expected to be a small
  constant factor, since arithmetic on large numbers is dominated by the
  big-number work itself.
- **What stays stuck on unknowns** follows the definitions. `OfNat a + OfNat b`
  computes to `OfNat (a + b)` for any `a`, `b`. `x + 1` with unknown
  `x : Int` is stuck. `OfNat x + NegSucc 2` is stuck on `x` (subtracting
  `3` needs to know whether `x ≥ 3`), but `OfNat (x + 5) + NegSucc 2`
  computes to `OfNat (x + 2)`, because `3 - (x + 5)` computes to `0` by
  `Nat.sub`'s definition.

### K2. A compact `Value::Int` with kernel natives — deferred

A `Value::Int` holding a signed big number, with natives for `Int.add`,
`Int.mul`, … under the whole-result obligation. Saves a few steps per
operation; costs a new value form (the full audit compact text needed) and a
new list of trusted natives. **Only if measurements show `Int` arithmetic
dominating checking or test time.** K1 costs nothing to undo: K2 could be
added later behind the same definitions, bound to them by content hash,
without changing any program's meaning.

## The definitions

A sketch of the prelude's `Std.Int`, following Lean's definitions [L2, L4]
adapted to Stitchwort. Exact names are suggestions; how a namespace's
declarations are written is [namespaces §4.3](namespaces.md#43-declaring-into-a-namespace).
The prelude's own definitions use constructors (`OfNat 0`, `NegSucc n`)
rather than `Int` literals, so they don't depend on the literal rules.

```
type Int : Type =
  | OfNat (n : Nat)
  | NegSucc (n : Nat)

-- `n.toInt`
Nat.toInt : Nat -> Int
Nat.toInt n = OfNat n

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

Int.mul : Int -> Int -> Int    -- by constructors first, so OfNat m * OfNat n = OfNat (m * n)
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
Text.toInt : Text -> Maybe Int  -- grammar in [Conversions]
```

**Division.** `Int.div` and `Int.mod` follow Lean's case split for `ediv`
and `emod` [L4]:

- **`d = OfNat Zero`:** `absurd (ok rfl)` ([Division by zero](#division-by-zero)).
- **Non-negative `a`, positive `d`:** `Nat`'s `/` and `%` on the
  magnitudes.
- **Negative `a = NegSucc m`, positive `d`:** quotient `NegSucc (m / d)`,
  remainder `d - 1 - m % d`. (The reviewer's check: writing
  `m = d·q₀ + r₀` gives `a = d·(−q₀ − 1) + (d − 1 − r₀)`, with the
  remainder in range.)
- **Negative divisor:** negate the quotient, leave the remainder unchanged.

Each case calls `Nat`'s division with a divisor of the form `Succ _`, for
which `auto` proves `!= 0` by computation.

**Decisions must stay small.** `Int.decEq` computes `Yes rfl` or a
constant-size `No`, never a proof as deep as a number:

- different constructors: `No` of a disjointness lemma
  (`Int.ofNatNotNegSucc`);
- same constructor: `Nat.decEq` on the fields, wrapped. `Yes p` becomes
  `Yes (Eq.cong OfNat p)`, which computes to `Yes rfl` on numbers; `No q`
  becomes `No (\h -> q (Int.ofNatInjective h))`, constant size since the
  `decEqNat` fix.

Draft 1 proposed testing this against a copy of the definition; as the
reviewer notes, a copy runs through the same `Nat` native and would share
any defect. The test is instead natives-on against natives-off, comparing
the complete `Yes`/`No` value including the proof
([Testing the definitions](#testing-the-definitions-r2)).

## Syntax and precedence

**Two new pieces of syntax:** prefix minus in expressions, and negative
number patterns.

**Precedence**, tightest first (new rows in bold):

| Level | Syntax | Associativity |
|---|---|---|
| 1 | atoms, `.field` and dot notation (`x.abs`, `p.pos.x`) | left |
| 2 | application (`f x y`) | left |
| **3** | **prefix minus (`-e`)** | **prefix, may repeat (`- -x`)** |
| 4 | `*` `/` `%` | left |
| 5 | `+` `-` | left |
| 6 | `++` | right |
| 7 | `=` `!=` `==` `<` `<=` | none |

So:

| Written | Means |
|---|---|
| `-x.abs` | `-(x.abs)`: dot binds tighter |
| `(-x).abs` | the absolute value of `-x` |
| `-f x` | `-(f x)`: application binds tighter |
| `f -x` | `f - x` (binary minus); write `f (-x)` |
| `-a * b` | `(-a) * b` |
| `a * -b` | `a * (-b)` |
| `-18 % 100` | `(-18) % 100`, which is `82` |
| `-(18 % 100)` | `-18` |
| `a - -b` | `a - (-b)` (with a space: `--` starts a comment) |

Prefix minus binds tighter than `*`, `/` and `%` so that `-18 % 100` means
what decision 1 says it means. Python makes the same choice (its unary minus
binds tighter than `%`, so `-18 % 100` is `82` there) [P1]; Haskell's
negation binds like binary minus, so ``-18 `mod` 100`` is `-(18 `mod` 100)`,
which is `-18`. For `*` the two readings give the same value; for `/` and `%`
they don't, which is why the choice matters.

**Where a prefix minus can appear:** at the start of an operand (the parser's
`mul_expr` operand position), so after `(`, `[`, `,`, a binary operator, `=`
in a definition, `then`, `else`, `->` and the like. Not as a function
argument: `starts_atom` doesn't include `-`, so `f -5` stays `f - 5`, as
today. AST: a new `Expr::Neg(Box<Expr>, Span)`.

**Negative literals** are `Expr::Neg` around `Expr::Num`. They mean the same
as `Int.neg` of the literal; the elaborator folds them into a constant
([Literals](#literals)).

**Patterns:** `(-k)` for a numeral `k`, in brackets in argument position
(`describe (-1) = …`). Only literals: `-` isn't a general pattern operator.
AST: `Pattern::Num` gains a sign (or a new `Pattern::NegNum`).

## Literals

Option 3 of draft 1 (type-directed literals) is adopted. All of this is in
the elaborator; the kernel only ever sees `Term::Nat k` for a `Nat` and
constructor applications such as `OfNat (Term::Nat 5)` for an `Int`.

**Checking a literal `k` against an expected type `E`:**

1. **Reduce `E`** to a head: force it, substitute solved metavariables and
   unfold definitions (as unification would), so an alias `Price = Int`
   counts as `Int`.
2. **`Nat`** (the registry's `Nat`): the number, as today.
3. **`Int`** (the registry's `Int`, by identity): `OfNat k`.
4. **An unsolved metavariable:** the literal is a `Nat`, and the
   metavariable is solved to `Nat` (today's behaviour). The elaborator
   remembers that this metavariable was solved by defaulting a literal, so
   a later mismatch can say why (see the limitation below).
5. **Anything else**, including a user's own type that happens to be named
   `Int`, and a type that can't be reduced to a head (`Family n` with `n`
   unknown): today's mismatch error, with a note that numerals can be a
   `Nat` or an `Int`.

**A negative literal `-k`:** checked against `Int` (after reduction) or an
unsolved metavariable, it's the constant `NegSucc (k - 1)`, **except
`-0`, which is `OfNat 0`**: zero is handled before subtracting one, since
`Nat` subtraction would turn `-0` into `NegSucc 0`, which is `-1`. Against
`Nat`, it's an error with a note: "a `Nat` can't be negative; use an
`Int`". Inferred with nothing expected, it's an `Int`.

**Inferring a literal** with nothing expected still gives `Nat`, so no
existing program changes meaning. But inside an arithmetic expression or a
comparison, bare literals are never inferred on their own: they wait until
the expression's number type is decided ([Numeric expressions](#numeric-expressions)).

**Expected types are propagated before anything defaults.** These come for
free from checking mode, since the existing elaborator already checks
constructor arguments and list items against the expected type:

```
(Just 5 : Maybe Int)        -- 5 is checked against Int: OfNat 5
([1, 2, 3] : List Int)      -- each item checked against Int
(MkPair 1 (-2) : Pair Nat Int)
```

They're tests, not new rules.

**The documented limitation.** Defaulting an unsolved metavariable at once
means a later argument can't change a literal's type. With

```
chooseFirst : [a : Type] -> a -> a -> a
chooseFirst x y = x
```

and `i : Int`, `chooseFirst 5 i` is rejected: checking `5` solves `a := Nat`,
and then `i` doesn't fit. The error says so:

```
error[E-TYPE-MISMATCH]: type mismatch
  | chooseFirst 5 i
  |               ^ this is an `Int`, but a `Nat` is expected here
  = note: `a` became `Nat` because of the literal `5`, checked before
          anything said otherwise; write `(5 : Int)`
```

and `chooseFirst (5 : Int) i` works. That's an inference limitation, not a
soundness or coercion issue; Lean avoids it by postponing literals, which
Stitchwort's elaborator can't do yet (it postpones only `auto` obligations).
Postponement can be added later: it only turns these errors into programs.

**The `3 - 5` trap.** `let d = 3 - 5` with no type anywhere is a `Nat`
subtraction, so `d` is `0`. That's today's behaviour, documented in
DESIGN.md §10; the fix is to say which type is meant, `let d : Int = 3 - 5`.
A warning for "a subtraction of literals that stops at zero" would be cheap
to add later.

## Numeric expressions

**Today** every arithmetic and comparison operator is bound to one `Nat`
definition, and `=` types its sides by whichever side it infers first. With
two number types, the type must be decided for the whole expression at
once, or `0 == x` would commit to `Nat` from the `0` before seeing `x`.

### Groups

A **group** is the unit that gets one number type. It's one of:

- **An arithmetic tree:** a maximal tree of `+ - * / %` and prefix `-`
  nodes. Brackets don't end it: `(a + b) * -c` is one tree.
- **A comparison:** `=`, `!=`, `==`, `<` or `<=`, together with the
  arithmetic trees on both sides. `x + 1 == y * 2` is one group.

Its **leaves** are everything else, in source order: literals, variables,
applications, `.field` and dot calls, `if`, `let`, annotations `(e : T)`,
and so on. A group never extends into a leaf: an argument such as the `a + b`
in `f (a + b) + c` is a separate group, checked against `f`'s parameter type,
and a variable is a leaf with whatever type its binding already has.

**Comparisons constrain their operands, not their result.** `<` gives a
`Prop` and `==` a `Bool`; an expected `Prop` or `Bool` says nothing about
the operands. Only an arithmetic tree uses its expected type.

### The rule

Elaborate a group, with an expected type `E` only for an arithmetic tree, as
follows. `T` is the group's operand type, initially undecided. Each decision
records what decided it (the expected type, a named operand, or a `-`), for
error messages.

1. **Expected type.** If `E` is given, reduce it (as for literals). `Nat`
   or `Int`: `T := E`. Any other known type: an error ("`+` gives a `Nat`
   or an `Int`, but a `Text` is expected here"). An unsolved metavariable or
   nothing: no decision.
2. **Minus signs.** If `T` is undecided and the group has a prefix `-`
   (including a negative literal): `T := Int`. If `T` is already `Nat`: an
   error at the `-` ("a `Nat` can't be negated; this expression is a `Nat`
   because …").
3. **Pass 1: leaves that can't default anything.** While `T` is undecided,
   take, in source order, each leaf that is an annotation `(e : A)` or
   contains no numeric literal at all (and isn't a lambda):
   - infer it (an annotation's type is `A`; its body is checked against `A`
     as usual), and reduce its type;
   - **`Nat` or `Int`:** `T :=` that type; pass 1 ends;
   - **an unsolved metavariable:** an *unknown* leaf; it doesn't decide
     anything, and pass 1 goes on;
   - **any other known type:** in a group with an arithmetic operator,
     a prefix `-`, `<` or `<=`, an error ("`+` works on `Nat` and `Int`;
     `t` is a `Text`"). In an equality (`=`, `!=`, `==` with no arithmetic
     on either side), `T :=` that type: generic equality, as today. A bare
     literal compared with it (`t == 0`) then fails at step 6 with the
     literal's mismatch error;
   - **can't be inferred** (`E-CANNOT-INFER`): left for step 5.
4. **Pass 2: the remaining leaves except bare literals**, in source order.
   If `T` is decided, check the leaf against `T`. If not, infer it and
   classify it as in pass 1.
5. **Default.** If `T` is still undecided:
   - look again at the unknown leaves, in order: their metavariables may
     have been solved by later leaves; the first that is now `Nat` or `Int`
     decides `T`;
   - otherwise, if the group has **numeric syntax** (a bare literal leaf,
     an arithmetic operator, `<` or `<=`; a literal *inside* a leaf, as in
     `Just 5`, doesn't count): `T := Nat`;
   - otherwise (an equality with no numeric syntax, such as `x = y` with
     both types unknown): `T` is the first leaf's type, exactly as
     `equation` does today.
6. **Finish the leaves.** Unify each inferred leaf's type with `T`; check
   each leaf left over (bare literals, leaves that couldn't be inferred)
   against `T`. A failure is a mismatch that names what decided `T`.
7. **Build.** Each arithmetic node applies `T`'s registry entry (`Nat.add`
   or `Int.add`, and so on, by identity); a prefix `-` applies `Int.neg`
   (folded to a constant for a literal); `<` and `<=` apply `T.LessThan` and
   `T.LessEq`; `/` and `%` insert their `auto` obligation `d != 0` at `T`.
   `=`, `!=` and `==` are built exactly as today, at `T`, so `==` still
   finds its decision procedure by `auto` for any type. If `E` was an
   unsolved metavariable, unify it with `T`.

Steps 3 to 5 are where an **unknown** type (a metavariable, which defaulting
may settle) differs from a **known unsupported** type (`Text`, which is an
error): the review's main point.

**Existing programs keep their meaning.** In a program with no `Int` in it,
every leaf is a `Nat`, a literal or unknown, and there's no prefix `-`
(it's new syntax), so every group's `T` is `Nat`, by a leaf or by the
default, and every operator is the same `Nat` definition as today. Equality
on other types decides `T` from the first leaf that can be inferred, as
`equation` does today; the one difference is that pass 1 may infer a
literal-free leaf on the right before a literal-containing leaf on the left,
which only matters when the left leaf's own inference would have defaulted
a literal. A snapshot run over every example confirms it
([Testing](#elaboration)).

### Worked examples

With `x i : Int`, `n : Nat`, `t : Text`:

| Expression | Decided by | Result |
|---|---|---|
| `x + 1`, `1 + x`, `0 - x`, `x * -2` | `x` (pass 1), or the `-` | `Int` |
| `pos % 100` with `pos : Int` | `pos` | `Int.mod pos (OfNat 100)`, `auto` proves `OfNat 100 != OfNat 0` |
| `x == 0`, `0 == x`, `0 != x`, `0 = x` | `x` | `Int` equality; the `0` waits for step 6 |
| `3 - 5 = -2` | the `-2` | `Int`: both sides are `Int`, and `rfl` proves it |
| `3 - 5` alone, or `let d = 3 - 5` | nothing: default | `Nat`, value `0` |
| `-(3 - 5)` | the `-` | `Int.neg (Int.sub 3 5)`, value `2` |
| `-n` | the `-` (step 2, before any leaf) | error: "`n` is a `Nat`; this is an `Int` because of the `-`; write `-(n.toInt)`" |
| `let m = 3 - 5` then `m + i` | `m` (a `Nat`, as bound) | error: "`i` is an `Int`, but this arithmetic is on `Nat` because of `m`"; the binding isn't reinterpreted |
| `n + i` | `n` | error with the hint "write `n.toInt`" |
| `n.toInt + i` | `n.toInt` | `Int` |
| `(if c then 1 else 2) + i` | `i` (pass 1, before the `if`) | `Int`: the `if` is then checked against `Int`, and so are its branches |
| `Just 5 == m` with `m : Maybe Int` | `m` (pass 1) | `Maybe Int` equality, with `Just 5` checked against it (rejected today) |
| `f 5 + i` with `f : a -> a` | `i` (pass 1) | rejected: checking `f 5` against `Int` still infers the application first (`fallback`), so the `5` defaults, as in `chooseFirst`; `f (5 : Int) + i` works |
| `List.map (\x -> x + 1) [1, 2]` | nothing (`x`'s type is a metavariable): default | `Nat`, as today |
| `(\(y : Int) -> y + 1)` | `y` | `Int` |
| `t + 1` | `t` | error: "`+` works on `Nat` and `Int`; `t` is a `Text`" |
| `x < 0` | `x` | `Int.LessThan x (OfNat 0)`; the result `Prop` isn't an operand type |
| `xs = []` (no numbers) | `xs` | generic equality, as today |
| `(x + 1 : Nat)` | the expected type `Nat`, then `x` fails | error: "`x` is an `Int`, but `Nat` is expected" |

### Unary minus

Prefix `-e` is part of its group and forces `Int`. So its operand is
*checked* at `Int` rather than inferred and then negated: `-(3 - 5)` is
`Int.neg (Int.sub (OfNat 3) (OfNat 5))`, which is `2`, not "negate the `Nat`
`0`". A `Nat` operand is the mixed-type error with a hint to write
`.toInt`. `x.neg` (`Int.neg x`) remains available by name.

### Bindings

The rule never looks through a binding. `let n = 3 - 5` elaborates `3 - 5` as
its own group, with no expected type, so `n : Nat` with value `0`; a later
`n + i` sees `n` as a `Nat` leaf and is a mixed-type error. The error names
`n` as the decider, so the fix (`let n : Int = 3 - 5`) is easy to find.

### Effects and evaluation order

**Runtime evaluation is left to right, as written, regardless of the order
in which the elaborator examines operands.** The elaborator only decides
types out of order; the term it builds keeps every operand in its source
position, and Stitchwort evaluates arguments left to right (and generated JS
does too).

In effectful code, `comp_compound` already runs effectful operands first,
left to right, binding each to a fresh variable. Two changes:

- It must **flatten through the whole group**: today it handles one
  `Expr::Binary` node, so an effectful operand inside a nested arithmetic
  node is elaborated as a separate expression. With groups, every effectful
  leaf of the group runs first, in source order, and the group is then
  typed as a whole, with those leaves as already-typed variables (decisive
  in pass 1).
- `Expr::Neg` joins the compound forms it handles.

An effectful leaf is therefore inferred on its own, before the rest of the
group: a literal *inside* it (`readOr 0`, for a polymorphic `readOr`)
defaults as in the `chooseFirst` limitation.

### Errors

New or changed diagnostics, each with a snapshot test:

- **Mixed number types** (`E-TYPE-MISMATCH`): names the leaf that doesn't
  fit, the type `T`, and what decided `T`; suggests `.toInt` (from `Nat`)
  or `Int.toNat`/`Int.toNatChecked` (from `Int`).
- **Unsupported operand type:** "`+` works on `Nat` and `Int`; this is a
  `Text`", listing the two types (today's error for `+` on a non-`Nat`,
  extended).
- **A negative literal or `-` at `Nat`:** "a `Nat` can't be negative; use
  an `Int`".
- **A literal defaulted too early:** the `chooseFirst` note above.

### How this relates to namespaces

Namespaces' reviewer question R6 asks whether "an operator means `T.op` for
the head `T` of its left operand's type" is the right direction
([namespaces §8](namespaces.md#8-extending-it-later-without-breaking-anything)).
This note's answer: the operand type is decided **per group, from all of
it**, not from the left operand, and the table is **closed** (`Nat`, `Int`),
like `++`'s. Each operator has one registry entry per number type
(`Builtin::Add` and `Builtin::IntAdd`, and so on), bound by identity.
Generalising to `T.add` for any `T` later is compatible: it only turns
"`+` works on `Nat` and `Int`" errors into programs.

## Conversions

| Function | Meaning | Notes |
|---|---|---|
| `Nat.toInt n` / `n.toInt` | `OfNat n` | A constructor, so free in JS and transparent in proofs |
| `Int.toNat x` | `x` if `x ≥ 0`, else `0` | Lean's name and behaviour; mirrors `Nat` subtraction's clamping |
| `Int.toNatChecked x` | `Just n` or `Nothing` | For when a negative value is a bug |
| `Int.natAbs x` | `|x|` as a `Nat` | The natural measure for recursion |
| `Int.abs x` | `|x|` as an `Int` | |
| `Int.sign x` | `-1`, `0` or `1` | |
| `Int.toText x` | decimal text | `"-42"`, `"0"`, `"17"`: no `+`, no leading zeros, never `"-0"` |
| `Text.toInt t` | `Maybe Int` | Grammar below |

**`Text.toInt`'s grammar**, exactly:

```
int    ::= "-"? digit+        -- the whole input, nothing before or after
digit  ::= "0" | "1" | … | "9"   -- ASCII only
```

- An optional **single** ASCII `-` (U+002D), then **at least one** ASCII
  decimal digit, and nothing else.
- **Leading zeros are allowed**, as `Text.toNat` (today's `textToNat`)
  allows them: `"007"` is `7`, `"-007"` is `-7`. So
  `Text.toInt (Int.toText x) = Just x` for every `x`, but not every text
  that parses is what `Int.toText` would print.
- **`"-0"` and `"-000"` are zero** (`OfNat 0`).
- **Rejected** (`Nothing`): `""`, `"-"`, `"+5"`, `"--5"`, `"- 5"`, `" 5"`,
  `"5 "`, `"0x10"`, `"1_000"`, `"5.0"`, and non-ASCII digits such as
  `"５"` (fullwidth) or `"٥"` (Arabic-Indic).
- **Definition:** `Text.toInt (MkText (Cons '-' cs)) = Maybe.map (\n -> Int.neg (OfNat n)) (Text.toNat (MkText cs))`,
  otherwise `Maybe.map OfNat (Text.toNat t)`. Since `Text.toNat` already
  rejects the empty text, `"-"` is `Nothing`, and `Int.neg` maps `0` to
  `0`.
- **In JS**, a native for `Text.toInt` (if one is written) tests the grammar
  explicitly (`/^-?[0-9]+$/`) before calling `BigInt`; `BigInt(s)` alone
  accepts more than this grammar (surrounding whitespace, `0x` prefixes, an
  empty string as `0n`).

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
constructor pattern around a `Nat` number pattern: `404` is `OfNat 404`,
`-1` is `NegSucc 0`, and `-0` is `OfNat 0` (zero special-cased, as for
literals). The existing pattern compiler then produces an ordinary `case` on
`Int` with a `NumCase` in each branch:

```
case x of
  OfNat m   -> NumCase(m, [(0, "zero"), (404, "not found")], "something else")
  NegSucc k -> NumCase(k, [(0, "minus one")], "something else")
```

**The pattern compiler's rule** (an addition to step 3 of
[number patterns' compiler](number-patterns.md#the-pattern-compiler)):

- A column whose type is the registry's `Int`, in which any row has an `Int`
  literal pattern, is split with a constructor `case` on `Int`. A literal
  `k ≥ 0` becomes `k` on the `OfNat` field; `-k` (`k ≥ 1`) becomes `k - 1`
  on the `NegSucc` field. Explicit `OfNat p` and `NegSucc p` rows pass `p`
  to the field. Variable and `_` rows go to both branches.
- Each branch's field column is then an ordinary `Nat` column, classified
  as today (a `NumCase` if it has numbers, a constructor split if it has
  explicit `Zero`/`Succ`). A branch with no number patterns is just its
  default rows, with no `NumCase` (the kernel refuses an empty table, and
  the compiler already never makes one).
- **Variables bind the original value** (number patterns' rule 6): in
  `pick z False = z`, `z` is the `Int`, not the field.
- The first-row base case, row priority and key merging are unchanged:
  repeated literals (`0` and `-0` included) merge into one key, and a
  catch-all before a literal makes the literal's row unreachable, as for
  `Nat`.
- `OfNat (-1)` is an error: the field is a `Nat`, and `-1` against `Nat` is
  the "a `Nat` can't be negative" error.

**What a catch-all learns** (corrected from draft 1). The outer split
*does* reveal the sign constructor: in the `NegSucc` branch, the value is
known to be `NegSucc k`. What the inner `NumCase` default doesn't provide
is equality to, or exclusion of, particular numbers. So with

```
zeroOrOther : Int -> Bool
zeroOrOther 0 = True
zeroOrOther _ = False
```

`zeroOrOther (NegSucc k)` computes to `False` even for unknown `k` (that
whole branch is the catch-all), while `zeroOrOther (OfNat m)` is stuck for
unknown `m`. The number-patterns policy otherwise carries over: a number
pattern tests for a value, `OfNat`/`NegSucc` patterns expose structure, and
`f (OfNat n)` / `f (NegSucc n)` remain the way to split on sign with
information.

**The mixed-column regression** (the reviewer's):

```
pick : Int -> Bool -> Int
pick (-1) True  = 7
pick z    False = z
pick _    _     = 9
```

`pick (-1) False = -1`, `pick (-2) False = -2`, `pick 3 False = 3`,
`pick (-1) True = 7`, `pick 3 True = 9`. This checks both row priority and
that `z` is the original integer, not the field.

In generated JS, the `case` on `Int` is a sign test on the `bigint`, and each
`NumCase` a `switch` on the field (see below). Switching on the `bigint`
directly (`case -1n:`) is a possible later optimisation, which the language
doesn't promise either way.

## Termination

`Int` isn't recursive: its constructors hold `Nat`s, not `Int`s. So a
function that recurses does so on a `Nat` it gets from the `Int`:

```
-- the sum 0 + 1 + … + n, or 0 + -1 + … + n for negative n,
-- where `Nat.triangle` is the same sum on naturals, recursing on its `Nat`
Int.triangle : Int -> Int
Int.triangle (OfNat n)   = (Nat.triangle n).toInt
Int.triangle (NegSucc k) = Int.neg (Nat.triangle (Succ k)).toInt
```

or with `Int.natAbs x` as fuel or a measure. The termination checker needs
no change.

## Proofs about integers

**What works immediately:** `rfl` on closed values (`3 - 5 = -2`,
`-18 % 100 = 82`), because the definitions compute on numbers through the
`Nat` natives; `==` and `if h : a = b` through `Int.decEq`; `auto` for
literal side conditions such as `100 != 0`; and `rfl` for facts that hold by
computation on unknowns, such as `n.toInt + m.toInt = (n + m).toInt`.

**A lemma checkpoint alongside the implementation**, as the reviewer
recommends, rather than a later stage. The bottleneck for using `Int` in
proofs is missing basic lemmas, not the absence of a solver.

*Checkpoint 1, with the type and its operations:*

- `Int.negNeg : (x : Int) -> Int.neg (Int.neg x) = x` (three cases)
- constructor facts: `Int.ofNatInjective`, `Int.negSuccInjective`,
  `Int.ofNatNotNegSucc`, `Int.negSuccNotOfNat` (also used by `Int.decEq`)
- `Nat.toInt` and the operations: `Int.toIntAdd : (m + n).toInt = m.toInt + n.toInt`
  and `Int.toIntMul` (both by `rfl`; stating them keeps the computation
  from silently breaking if a definition's case order changes)
- round trips: `Int.toNat n.toInt = n`, `Int.toNatChecked n.toInt = Just n`,
  `Int.natAbs n.toInt = n`, `Int.natAbs (Int.neg x) = Int.natAbs x`

*Checkpoint 2, with division:*

- the division law: `Int.divAddMod : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> d * (a / d) + a % d = a`
- remainder bounds: `0 <= a % d` and `a % d < (Int.natAbs d).toInt`
- `Int.modNatLt : (x : Int) -> (d : Nat) -> [auto ok : d != 0] -> x.modNat d < d`,
  the fact the dial program needs (`(pos - n.toInt).modNat 100 < 100`)
- `Int.modNatToInt : (x.modNat d).toInt = x % d.toInt` (the `%` side's
  `d.toInt != 0` comes from `ok` through a small lemma
  `Nat.toIntNeZero : d != 0 -> d.toInt != 0`, passed by name)
- `n.toInt / d.toInt = (n / d).toInt` and the same for `%`

These need `Nat` lemmas the prelude doesn't have yet: the `Nat` division law
(`d * (n / d) + n % d = n`, through `divFuel`), `n % d < d`, and the usual
facts about `+`, `*` and `-` (commutativity, associativity, cancellation).
**Stitchwort's `Nat` lemma library is thin today**: the prelude has
injectivity and disequality lemmas but not `Nat.add` commutativity or any
division law. So checkpoint 2 starts with those. This is the main cost of
integers, and it's the same with every representation.

**Not proposed:** a decision procedure for linear arithmetic (`omega`,
`lia`). A solver can follow when repeated range and linear-arithmetic proofs
show the need; having `Int` is a prerequisite for one [L7, R4].

## The JavaScript boundary and generated code

**Representation.** An `Int` is a `bigint` of either sign everywhere in
generated code, as `Nat` is a non-negative `bigint`:

| Stitchwort | Generated JS |
|---|---|
| `OfNat n` | `n` |
| `NegSucc n` | `-n - 1n` |
| matching `x` on `Int` | `if (x >= 0n) { const n = x; … } else { const n = -x - 1n; … }` |
| `n.toInt` | `n` (no code) |
| `Int.OfNat`, `Int.NegSucc` as values | `(n) => n`, `(n) => -n - 1n` |

**This is a bijection** between `Int` values and `bigint`s:
`OfNat n ↔ n` covers the `bigint`s `≥ 0n`, `NegSucc n ↔ -n - 1n` covers those
`≤ -1n`, and the sign test recovers the constructor and field (`-x - 1n`
inverts `-n - 1n`). So the encoding is lossless and needs no tag. It's the
same kind of special case as `Nat`'s (a registry-identified data type
compiled to a primitive), in the trusted extractor.

**Boundary.** `.d.ts` type `bigint`. Decoding is strict, like `Nat`'s and
`Text`'s: anything that isn't a `bigint` (including a `number` such as `5`,
and a numeric string) is refused with `StitchwortInputError` ("expected a
bigint"). Encoding can't fail. **`Nat` and `Int` share a JS representation
but not a validator:** a `Nat` position still refuses `-1n`, an `Int`
position accepts it, including inside records, lists and `Maybe`.

**Preconditions.** An exported function's `[auto ok : d != 0]` at `Int`
becomes a runtime check before the call ([Division by zero](#division-by-zero)).

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
The proof arguments (`ok : d != 0`) are erased too; a native is only reached
with a divisor that has a checked proof, or that a boundary validator has
just checked, so it can't throw `RangeError`.

A wrong JS native gives a wrong answer in JS, not a false theorem
(DESIGN.md §13's "native text in extracted JS" row is the precedent).

**Two separate fallbacks.** The content-hash binding guards two different
things, and a mismatch in each has a different consequence:

- **An operation's hash doesn't match** (someone changed `Int.add`'s
  definition): that native is not used, and `Int.add` is compiled from its
  definition, as written, on the `bigint` representation. Every other
  native and the representation are unaffected.
- **The `Int` data type's hash doesn't match** (its constructors, their
  order or their fields changed): the `bigint` representation, the
  constructor and matching code above, the boundary codec and `.d.ts` type,
  and every `Int` operation native are **all disabled together**. `Int` is
  then compiled as an ordinary data type with the ordinary data codec. They
  are one contract: compiling constructors generically while keeping a
  `bigint` boundary (or the reverse) would decode values wrongly.

In both cases a test fails, printing the new hashes, so a deliberate prelude
change forces someone to re-check the natives.

## Hashing and binding

- **No new hashing rules.** `Int` is a data type; `-5` elaborates to the term
  `NegSucc 4`, which is hashed like any constructor application around a
  number. Two spellings of the same value (`-5` and `Int.NegSucc 4`) give
  the same term, so the same hash.
- **Syntax** (literals at `Int`, negative literals, `Int` patterns, the
  `Int` operator entries) binds to `Std.Int` declarations through the
  registry, by identity, so a user's own `Int` or `add` changes nothing
  (namespaces stage 0's invariants). New registry entries: the `Int` data
  type and its two constructors; `Int.neg`, `Int.add`, `Int.sub`,
  `Int.mul`, `Int.div`, `Int.mod`, `Int.LessThan`, `Int.LessEq`.
- **Names:** `Int` is in the default set (namespaces D4: core types);
  its constructors are written `Int.OfNat` and `Int.NegSucc` in user code,
  since `OfNat` alone is too generic a name to make default-visible. (A
  namespaces question, recorded here; the patterns above work either way.)
- **JS natives and the `bigint` representation** are bound by content hash
  to the declarations they were written for, with the two fallbacks above.
- **Kernel:** nothing to bind under K1.

## Trusted code

| Component | Change | Trusted? |
|---|---|---|
| Kernel (checking, evaluation, conversion, hashing) | **None** under K1 | — |
| Kernel natives | None; the existing `Nat` natives are exercised in new shapes, and tested in them | Already trusted |
| Prelude `Std.Int` definitions | New, ordinary definitions | No: checked by the kernel. Their *meaning* is the specification, as for `Nat` |
| Elaborator: literals at `Int`, negative literals, unary minus, numeric groups, `Int` patterns | New | No: the kernel re-checks the output |
| Registry entries for `Int` | New | No more than today's (identity only) |
| Extractor: `Int` as `bigint`, its matching and constructors, boundary codec, validators | New | Yes, like `Nat`'s (DESIGN.md §12–§13: the extractor and codecs are trusted) |
| JS natives for `Int` operations | New, about ten one-liners | Yes, in JS only: a bug is a wrong JS answer, not a false theorem |
| Printer (`-5` rather than `NegSucc 4`) | New | No |

So the kernel's trusted base doesn't grow. The extractor's does, by about as
much as `Nat` added.

## Testing

### Testing the definitions (R2)

These guard the claim that K1 adds no mismatch, by exercising the `Nat`
natives in the shapes `Int` uses. **"Same result" always means the complete
normal form**, quoted and compared as a term (including proofs inside
`Yes`/`No`, and including *where* a term is stuck), not a Boolean or a
decoded number.

1. **Small, exhaustive, natives on versus natives off.** Every operation
   (`neg`, `add`, `sub`, `mul`, `leq`, `compare`, `decEq`, `div`, `mod`,
   `tdiv`, `tmod`, `fdiv`, `fmod`, `modNat`, `subNatNat`) on all arguments
   in `-12..12` (divisors non-zero), evaluated with every kernel native on
   and with every native off, in both evaluators (the machine and
   `reference.rs`). Natives off means unary arithmetic, so the range stays
   small.
2. **Named edge cases, both modes:**
   - `Int.subNatNat 0 n`, `Int.subNatNat n 0`, `Int.subNatNat (Succ n) (Succ m)`
     and `Int.subNatNat n n`;
   - `Int.add (OfNat n) (NegSucc m)`, both orders, with `n` above, equal to
     and below `m + 1`;
   - `Int.decEq (NegSucc n) (NegSucc m)` and `Int.decEq (OfNat n) (NegSucc m)`,
     comparing the full `Yes`/`No` value;
   - the division cases on each side of zero, and `-1`/`1` divisors.
3. **Open terms, both modes:** the same expressions with **rigid variables**
   (`n`, `m` bound by a lambda or a theorem's parameters), and with **partly
   known** arguments in `NatAdd` shape: `Int.add (OfNat (n + 5)) (NegSucc 2)`
   must compute to `OfNat (n + 2)`, while `Int.add (OfNat (n + 2)) (NegSucc 5)`
   must stay stuck, with the *same* stuck term in both modes.
4. **Metavariables (elaborator tests):** an `rfl` or `==` whose sides contain
   an `Int` operation on a metavariable, both **before** and **after** the
   metavariable is solved in the same declaration. For example, with
   `check4 : (a : Nat) -> Int.subNatNat a 1 = OfNat 4 -> Unit`,
   `check4 _ rfl` must fail with "can't work out" (the elaborator must not
   solve `a` by inverting `subNatNat`), while `check4 5 rfl` succeeds; and
   the same with the metavariable solved by a later implicit argument
   before the `auto` obligations are proved. Run with natives on and off.
5. **Large values, against an independent implementation.** Values around
   `±2^64`, `±2^128`, `±2^256` and seeded random large values, natives on,
   compared with `num_bigint::BigInt` in the test, where the Euclidean,
   flooring and truncating results are computed from `BigInt`'s own
   division independently of the prelude (Leijen's formulas, written again
   in Rust). Not natives off: unary arithmetic near `2^64` isn't feasible.
   For `decEq` on large values, check the tag and that the proof term has
   constant size.

### Elaboration

- Every example in [Worked examples](#worked-examples), accepted with the
  stated type and value or rejected with the stated error (snapshots).
- Literals: `Just 5 : Maybe Int`, `[1, 2, 3] : List Int`,
  `MkPair 1 (-2) : Pair Nat Int`; an alias `Price = Int` takes literals;
  a user `type Int = …` doesn't (mismatch), and doesn't change what the
  built-in literals mean; `-0` is `OfNat 0`; `-1 : Nat` rejected.
- The limitation: `chooseFirst 5 i` rejected with the note;
  `chooseFirst (5 : Int) i` and `chooseFirst i 5` accepted.
- Precedence: `-x.abs` versus `(-x).abs`; `-f x`; `f (-5)` versus `f -5`;
  `-18 % 100 = 82` and `-(18 % 100) = -18` by `rfl`; `-a * b`; `a - -b`.
- Unary minus: `-(3 - 5) = 2` by `rfl`; `-n` for `n : Nat` rejected.
- Bindings: `let n = 3 - 5` then `n + i` rejected naming `n`;
  `let n : Int = 3 - 5` then `n + i` accepted.
- Effects: an arithmetic group with effectful leaves on both sides of a
  nested node runs them left to right (observed through an ability that
  records order), and `-` around an effectful call.
- **Every existing example and test elaborates to the same terms**: hashes
  of all existing declarations unchanged (the strongest check that the `Nat`
  default really is today's behaviour).

### Patterns

- `describe` in both evaluators and in JS.
- `zeroOrOther (NegSucc k)` computes to `False` for an unknown `k`;
  `zeroOrOther (OfNat m)` stays stuck.
- `pick`'s five results above.
- Repeated literals in different rows; `0` and `-0` in one column (one key);
  a very large negative key (`-10^30`); a catch-all before literals
  (unreachable rows, as for `Nat`); `OfNat (-1)` rejected; a column mixing
  `0`, `-1`, `OfNat n` and `_`; two `Int` columns.

### Division

- `x / 0` at `Int` rejected (`auto` finds `0 != 0` false);
  `if h : d != 0 then a / d else 0` accepted and run (kernel and JS).
- An exported `safeDiv : (a : Int) -> (d : Int) -> [auto ok : d != 0] -> Int`
  called from Node with `0n`: `StitchwortInputError`, no `RangeError`.
- Leijen's table for all four conventions, by `rfl`.

### Extraction

- **JS natives against their definitions** compiled without natives, under
  Node, on the inputs of the R2 tests: the existing differential-extraction
  tests, extended.
- **Through ordinary user code**, not only native arithmetic: constructor
  functions passed as values (`List.map Int.OfNat [1, 2]`,
  `List.map Int.NegSucc [0, 4]` giving `[-1n, -5n]`); pattern matching on
  native results (`case a % d of …`); nested `Maybe Int` and `List (Maybe Int)`
  across the boundary; a record with a `Nat` field and an `Int` field,
  where `-1n` is accepted in the `Int` field and refused in the `Nat` one.
- **Boundary:** negative and positive `bigint`s round-trip; `5`, `"5"`,
  `5.0`, `null` refused.
- **Fallbacks:** with a test-only change to `Int.add`'s body, only that
  native is off and results are unchanged; with a change to the `Int` data
  type, the representation, codec and natives are all off together, the
  generated code is self-consistent, and the hash test fails printing the
  new hashes.
- **`Text.toInt`:** every example in its grammar, in the kernel and in JS
  (natives on and off); `Text.toInt (Int.toText x) = Just x` on the R2
  inputs.

### Must reject (DESIGN.md §13 style)

Each paired with an accepted neighbour: `x / 0` at `Int`;
`bad : (x : Int) -> x % 3 = OfNat 1` by `rfl`; `-1 : Nat`;
`Int.neg x = x` by `rfl` for unknown `x`; `Int.neg (Int.neg x) = x` by
`rfl` for unknown `x` (it's `Int.negNeg`, a theorem).

### Example programs

The dial (with `Int.modNatLt` used in a proof), and a grid walk with
negative coordinates.

## Implementation plan

**Prerequisite:** namespaces stage 1 merged (`Std` namespaces and the
registry the `Int` entries join). Dot notation (namespaces stage 2) makes
`n.toInt` and `x.abs` read well but isn't required: `Nat.toInt n` works
without it, and the precedence tests for `-x.abs` wait for it.

**Who does what.** The implementer is an Opus agent that delegates
mechanical parts to a Sonnet worker. Below, **[think]** marks parts that
need design judgement (elaboration rules, kernel interaction, proofs) and
that the Opus agent should write itself; **[mech]** marks parts that are
mechanical once specified (library boilerplate, JS codec plumbing, tests
from a given list, docs), suitable for the Sonnet worker. For each [mech]
task, the Opus agent hands over the exact file list and expected results
from this note, and reviews the diff; if the worker meets a case this note
doesn't cover, it stops and reports rather than deciding. Each stage ends
with the repository's usual gate, and is committed separately.

**Stage 1: the type and its library** (no new syntax; the prelude uses
constructors)

- [think] `Int`, `Int.neg`, `Int.subNatNat`, `Int.add`, `Int.sub`, `Int.mul`,
  `Int.decEq` (constant-size proofs, as specified in
  [The definitions](#the-definitions)), and the four divisions with the
  explicit zero branch. These are where the `Nat` natives get called in new
  shapes.
- [mech] The rest of the library from the sketch: `Int.leq`, `LessThan`,
  `LessEq`, `compare`, `natAbs`, `abs`, `toNat`, `toNatChecked`, `sign`,
  `modNat`, `toText`, `Text.toInt` (grammar given), `Nat.toInt`.
- [mech] Registry entries for the type, constructors and operator
  definitions; printing closed `Int` values as `-5` and `5`.
- [think] R2 tests 2–4 (the edge cases and open terms, where the expected
  stuck terms have to be worked out), and the natives-off harness if the
  existing one doesn't fit.
- [mech] R2 tests 1 and 5 (the exhaustive grid and the `num_bigint`
  comparison), from the specification above.
- [think] Lemma checkpoint 1.

**Stage 2: syntax** (parser and AST only; the elaborator rejects the new
forms with a "not yet" error until stage 3)

- [mech] `Expr::Neg` at the precedence in
  [Syntax and precedence](#syntax-and-precedence), negative number patterns,
  and parser tests from the precedence table (including `f -5` staying
  binary and `--` staying a comment).

**Stage 3: elaborating numbers** (the core of the work)

- [think] Literals at `Int`, negative literals with the zero case, reduction
  of the expected type, the "defaulted literal" note.
- [think] Groups and the rule (steps 1–7), replacing the fixed-`Nat`
  operator case and `equation`'s typing of `=`, `!=`, `==`; unary minus;
  `comp_compound` flattening through groups, with `Expr::Neg` added.
- [think] Diagnostics: mixed types naming the decider, unsupported types,
  negative at `Nat`.
- [mech] The elaboration tests from [Elaboration](#elaboration), as
  snapshots, from the worked-examples table; the check that every existing
  declaration's hash is unchanged.

**Stage 4: patterns**

- [think] The `Int` column split in the pattern compiler (variables binding
  the original value, rows going to both branches, `-0`).
- [mech] The pattern tests from [Patterns](#patterns), in both evaluators.

**Stage 5: JavaScript**

- [think] The two-level hash binding (representation contract versus
  operation natives) and where the extractor's `Nat` special case is
  generalised; the Opus agent should also review all trusted extractor code
  in this stage, since it's in the trusted base.
- [mech] `bigint` constructors and matching, the boundary codec and `.d.ts`,
  the operation natives (formulas given above), `Text.toInt`'s native if
  any, the validator for `d != 0` at `Int`.
- [mech] The extraction, boundary, division and fallback tests from
  [Extraction](#extraction) and [Division](#division).

**Stage 6: lemma checkpoint 2**

- [think] The `Nat` lemmas (division law, `n % d < d`, the arithmetic
  facts they need), then the `Int` division law, remainder bounds,
  `Int.modNatLt`, `Int.modNatToInt`, and the `toInt` compatibility of `/`
  and `%`. Proof work; it can run in parallel with stage 5.
- [mech] The dial and grid example programs, once the lemmas exist.

**Stage 7: documents**

- [mech] DESIGN.md, docs/syntax.md and docs/core.md, per
  [Documents to update](#documents-to-update); this note's "As built"
  section. The Opus agent reviews for accuracy against what was built.

**Later, separately:** measure, and consider K2 only if `Int` arithmetic
shows up in profiles; postponed literals; fixed-width types; implicit
`Nat` → `Int` coercions; operators for user types; a linear-arithmetic
decision procedure.

## Recommendation

- **Representation A** (`OfNat Nat | NegSucc Nat`) and **K1** (no kernel
  change): approved by the review.
- **Euclidean `/` and `%`**, `Int`-valued `%` plus `Int.modNat`, general
  unary minus: the user's decisions, unchanged.
- **Literals** typed by context, defaulting to `Nat` only when nothing
  decides, with the `chooseFirst` limitation documented.
- **One number type per group** (arithmetic trees and comparisons), decided
  from the expected type, the operands and minus signs, in two passes;
  `==` stays generic.
- **`bigint`** for `Int` in generated JS and at the boundary, with
  separately gated representation and operation natives.
- **Lemmas alongside implementation**, no solver yet.
- **Implement** in the seven stages above, after namespaces stage 1.

## The reviewer's questions, answered

Kept for the record; the answers are the review's, as adopted above.

- **R1. Representation.** Is A worth its asymmetric negation? *Yes; costs
  are library work (`subNatNat`, extra zero/successor splits).*
- **R2. No kernel natives (K1).** Could `Int` expose a whole-result
  discrepancy the `Nat` tests don't cover? *Not if the `Nat` natives are
  right, but the tests are evidence, so add the new-shape tests; keep K2
  deferred.*
- **R3. Literals.** Default to `Nat` on an unsolved metavariable? *Yes for
  now, with the limitation documented and tested, and known expected types
  propagated first.*
- **R4. Operators.** "Expected type, else first non-literal leaf"? *No:
  collect constraints across the expression, distinguish unknown from
  unsupported, coordinate equality and comparisons, specify unary minus and
  precedence.* A closed per-type table is the right first step.
- **R5. Division.** E rather than F, and `%` as `Int`? *Yes; formulas
  checked; make the zero branch explicit, validate at the boundary, connect
  `%` and `modNat` by a theorem.*
- **R6. Number patterns.** Constructor split plus `NumCase`? *Yes; correct
  the catch-all wording; add the listed tests. No signed `NumCase`.*
- **R7. Extraction.** Direct `bigint`? *Yes; separate the representation
  and operation fallbacks; test through user code; exact `Text.toInt`
  grammar.*
- **R8. Proof support.** When does the lack of a solver bite? *Not first:
  basic lemmas do. Bring a small set forward, then division and bounds.*

## Documents to update

When built:

- **DESIGN.md §10:** `Int` division becomes Euclidean, with the truncating
  and flooring variants named; drop "matches JS `BigInt` so extracted code
  can use the native operators directly". Literals typed by context; the
  `3 - 5` trap.
- **DESIGN.md §12:** `Int` moves from planned to supported in the boundary
  table; the note "`Int` division and remainder are defined to match
  `BigInt`'s" changes.
- **DESIGN.md §13:** the native-arithmetic row mentions that `Int` has no
  kernel natives; the extracted-JS natives row gains the `Int` natives and
  the two fallbacks.
- **docs/syntax.md:** literals, negative literals, unary minus and its
  precedence, numeric groups, `Int` patterns.
- **docs/core.md "Numbers":** `Int` as a data type over `Nat`.
- **namespaces.md §4.7 and §8:** the per-type operator entries, and R6's
  answer.

## What I couldn't verify

- **No measurements.** Nothing was built or run for this note. The claim
  that K1 costs only a small constant factor per operation is an estimate
  from the definitions' shape.
- **The JS division formulas** were checked by the reviewer (49,742 pairs,
  Node 22.16.0), not re-run for this draft.
- **The rule's claim that existing programs keep their meaning** is argued
  from the rule, not tested; stage 3's unchanged-hashes test is what
  confirms it.
- **The open-term example** (`OfNat (n + 5) + NegSucc 2` computing to
  `OfNat (n + 2)`) is worked out by hand from `Nat.sub`'s definition and
  `Value::NatAdd`'s meaning, not run.
- **Python's precedence** (unary minus tighter than `%`) and **Haskell's**
  (negation at the level of binary minus) are stated from memory and the
  Python reference cited for `%` [P1]; the precedence tables weren't
  re-fetched for this draft. Neither affects the design, which follows from
  decision 1.
- **What `BigInt()` accepts** beyond the `Text.toInt` grammar (whitespace,
  `0x`, empty string) is from memory of the ECMAScript `StringToBigInt`
  rules, not re-checked. The design doesn't depend on it: the native tests
  the grammar first.
- **Boute's paper itself** wasn't read: its content is cited through
  Leijen's note [D1], SMT-LIB [S1] and the Rocq documentation [R3].
- **Lean's `omega`:** described from the frontend source's own doc comment
  [L7], not the official docstring.
- **Lean's kernel list of accelerated `Nat` operations** comes from the
  kernel source [L3]; the reference manual lists fewer.
- **Agda's division convention** is inferred from the types and lemmas in
  `Data.Integer.DivMod` [A3], not from a stated definition.
- **Idris 2's and F\*'s division semantics** weren't checked.
- **Rocq's default `Z.div`** is described as floor from the comment in
  `ZDivEucl` [R3].
- **Advent of Code 2025 day 1, part 2** wasn't read; only part 1's dial is
  used here.

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
  built-ins: "The primitive implementation is used to evaluate applications
  to closed terms, and the Agda definition is used otherwise."
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
  `xH`), `N`, and `Z` (`Z0`, `Zpos`, `Zneg`).
  <https://rocq-prover.org/doc/master/corelib/Corelib.Numbers.BinNums.html>
- **[R2]** Rocq reference manual, *Primitive objects*: "These primitive
  declarations are regular axioms. As such, they must be trusted".
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
  infinity".
  <https://www.haskell.org/onlinereport/haskell2010/haskellch6.html>
- **[H2]** Haskell 2010 Report, §4.3.4: without a default declaration, a
  module behaves as if it had `default (Integer, Double)`.
  <https://www.haskell.org/onlinereport/haskell2010/haskellch4.html>
- **[P1]** Python language reference, *Expressions*: floor division; `%`
  "always yields a result with the same sign as its second operand (or
  zero)"; `x == (x//y)*y + (x%y)`; the operator precedence table (unary
  `-` above `*`, `/`, `//`, `%`; not re-fetched for draft 2).
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
  "algorithm E" for Euclidean division from truncating division.
  <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/divmodnote.pdf>
- **[AoC1]** Advent of Code 2025, day 1, *Secret Entrance* (part 1): a dial
  0–99 starting at 50, rotations such as `L68`, "turning the dial left from 0
  one click makes it point at 99".
  <https://adventofcode.com/2025/day/1>
- **External review**, 16 October 2026 (not in the repository): answers to
  R1–R8, including the JS division check and the test lists adopted here.
- This repository: [native-numbers.md](native-numbers.md),
  [number-patterns.md](number-patterns.md),
  [compact-text.md](compact-text.md), [namespaces.md](namespaces.md)
  (§4.7, §4.8, §8, R6), DESIGN.md §10, §12, §13,
  `crates/core/src/native.rs`, `crates/core/src/registry.rs`,
  `crates/core/src/globals.rs`, `crates/elab/src/check.rs` (`Expr::Num`,
  the operator case, `equation`, `append`, `fallback`),
  `crates/elab/src/effects.rs` (`comp_compound`, `run_first`),
  `crates/elab/src/auto.rs`, `crates/elab/src/lib.rs` (`add_validators`),
  `crates/syntax/src/parser.rs` (`cmp_expr` … `atom`), and the prelude
  (`crates/elab/src/prelude.sw`: `Nat`, `sub`, `div`, `mod`, `textToNat`).
