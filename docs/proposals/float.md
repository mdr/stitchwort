# Proposal: `Float`, a JavaScript number

**Status:** draft 1, 23 October 2026. Design-review gate: nothing is implemented. Follows D645 (a
JS-number `Float`). New decisions D680 to D689 ([§8](#8-decisions)). Written against commit
`421cd172`.

Labels: **[checked]** (read in this repository, `file:line`), **[reported by the port
analysis]** (measured or checked by a separate analysis of the motivating app, not re-run here),
**[run]** (run while writing this:
Node 22.23 and rustc 1.99 on macOS/arm64), **[cited]** (read in the source linked in
[Sources](#sources)), **[inferred]** (my reading, not stated anywhere), **[unverified]** (from
memory, not re-checked).

## 0. Summary

A real-world TypeScript app is being ported so that its exported Stitchwort code can be called
directly from TS. Its data has millisecond times that are sometimes fractional (`80281.87`, from
unrounded audio clock arithmetic), and the code adds, subtracts and compares them. Today a number at
the JS boundary is a `bigint` (`Nat`, `Int`) or a whole `number` (`SafeNat`, `SafeInt`, fractions
refused, [checked] `crates/js/src/lib.rs:2510-2530`), so these values can't cross.

The proposal, in one paragraph:

- **`Float`** in `std/Float`, a 64-bit IEEE double. At run time it is the real JS `number` (and a
  Rust `f64` in the runtime). It crosses the boundary as `number` (finite on the way in).
- **In the logic** it is a record of the double's 64 bits, `{ bits: Nat, valid: … }`, with exactly
  one NaN. This is the shape Lean 4 uses today [cited]. Equality, a total order, negation, absolute
  value and the IEEE comparisons are ordinary Stitchwort definitions over the bits, so they can be
  reasoned about. The rounding operations (`+ - * / %`, `floor`, `round`, conversions) are
  **bodyless primitives**: the checker computes them on literals with Rust `f64`, and otherwise
  treats them as unknown functions.
- **Operators match JS:** `+ - * / %` are the IEEE operations, in the order written. `==`, `!=`,
  `<` and `<=` on `Float` mean what `===`, `!==`, `<` and `<=` mean in JS (`NaN == NaN` is false,
  `0.0 == -0.0` is true). The proposition `x = y`, `DecEq` and derived equality mean "the same
  double", like `Object.is`. This split is the main decision (D683).
- **Proofs:** stage 1 proves structural facts (a filter keeps only times after `start`; a sort's
  output is sorted by `Float`'s total order) and facts about literals by computation (`0.1 + 0.2 =
  0.30000000000000004` by `rfl`). Facts needing algebra (`(t - s) + s = t`) are false for
  doubles and are proved for exact types, through code written over a small operations interface.
- **Later, not now:** giving the rounding operations real definitions over the bits (Lean's model,
  or Flocq's), which would turn the primitives into ordinary natives bound by hash.

## 1. How other languages do it

| Language | Float type | In the logic | Equality |
|---|---|---|---|
| **Lean 4** | `Float`, a structure over `Float.Model`, "a subtype of `UInt64`" where "bit patterns encoding a `NaN` must be exactly a chosen canonical `NaN`" [cited] | `add`, `sub`, `mul`, `div`, `sqrt` and the integer conversions "have a logical model in terms of `Float.Model`" and are compiled to C operators; `pow`, `exp`, `round`, `floor`, `toString`, trig "do not reduce in the kernel" [cited]. The reference says the model is not meant for lemmas: "not a goal … to have any direct lemmas written about it at all" [cited] | `==` is IEEE, "not a reflexive relation"; "floating-point equality does not correspond with propositional equality" [cited]. Whether `DecidableEq Float` exists: [unverified] |
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
   `eqb`s, F\*'s `ieee_eq`/`bit_eq`, Agda's primitive vs. word equality, Lean's `==` vs `=`).
3. **Nobody proves algebraic laws about doubles in everyday code.** The full models (Flocq,
   Isabelle) exist for numerical-analysis proofs, and Lean says outright its model isn't for lemmas.
4. The JS-targeting languages all take JS numbers as they are, NaN and all.

## 2. The type and its syntax

### 2.1 Name and place

`Float` (D680), in `std/Float/Float.sw`, loaded on import like `SafeInt` ([checked]
`crates/elab/src/std/Int/Safe.sw:14`). `Float` is what Lean, Agda, Elm and ReScript call it [cited],
and what a TS programmer expects. `Number` reads well in TS but clashes with the general idea of
"a number" in the docs; `F64` is precise but unfamiliar outside Rust.

### 2.2 The definition

```
-- A 64-bit IEEE 754 double: its bits, with every NaN as the one NaN (0x7FF8000000000000).
type Float = { bits: Nat, valid: Float.isValid bits = True }
```

`Float.isValid n` is `n < 2^64` and, if `n` is a NaN pattern, `n = 0x7FF8000000000000`. Two
doubles are equal as values (`x = y`) exactly when their bits are, so `0.0` and `-0.0` are
different values and there is one NaN, equal to itself. This is `Object.is` [inferred].

### 2.3 Literals

- **Forms:** `1.5`, `80281.87`, `0.25`, and with an exponent `1e3`, `1.5e-7`, `2.0E21` (D686).
  A digit is required on both sides of `.`, so `5.` and `.5` stay errors, and `x.name` and
  `List.map` are untouched (`.` after a digit is lexed as part of a number only when a digit follows;
  today a number is digits only, [checked] `crates/syntax/src/lexer.rs:245-252`).
- **Meaning:** the double nearest the decimal value, ties to even: what a JS literal or
  `Number("80281.87")` gives. Rust's `str::parse::<f64>` agrees: `80281.87` is bits
  `4680253341308362424` in both [run]. Rust's parser has been correctly rounded since 1.55
  [unverified]; the differential test in §7 checks it on many strings anyway.
- **Negative literals** are `-` applied to a literal, which is exact for doubles.
- **Lexing:** a new token `Tok::Float` holding the source text; the AST keeps the text and the
  elaborator parses it (so error spans and printing keep what was written).

### 2.4 Groups and defaulting

Today a group of `+ - * / %` and comparisons gets one operand type, defaulting to `Nat`
([checked] `crates/elab/src/numbers.rs:1-11`). Add a third kind, `Kind::Float`:

- A literal with `.` or an exponent **forces** the group to `Float`, as a prefix `-` forces `Int`
  today. So `t + 0.5` and `1.5 * 2` are `Float`.
- A whole literal in a `Float` group is a `Float`: `t - 1000` with `t: Float` is fine. A whole
  literal that isn't exactly a double (above 2^53 and not representable) is refused, with the
  nearest double in the message: JS would round it silently, but a ported program has no reason to
  write one [recommended in D686].
- No mixing: `t + n` with `t: Float`, `n: Int` is the existing mismatch error, and the fix is
  `t + Float.ofInt n`. TS has no `Int`, so the port never needs a silent conversion.
- **Why a new kind rather than instances:** `+` and `*` on other types go through `Add` and `Mul`
  ([checked] `numbers.rs:323`), and those interfaces carry laws: `zeroAdd`, `assoc`, `comm`
  ([checked] `crates/elab/src/std/core/AddMul.sw:9-25`). Doubles break them: `(0.1 + 0.2) + 0.3`
  ≠ `0.1 + (0.2 + 0.3)`, and even `0.0 + -0.0` is `0.0`, not `-0.0` (`zeroAdd` fails) [run].
  `-`, `/` and `%` are on `Nat` and `Int` only ([checked] `numbers.rs:892`). So `Float`'s operators
  are built directly, as `Int`'s are when no dictionary applies.
- `/` and `%` on `Float` need **no** proof that the divisor isn't zero: `1.0 / 0.0` is `Infinity`
  and `0.0 / 0.0` is NaN, as in JS.
- Evaluation order and grouping are kept: the group builds the term with every leaf in place
  ([checked] `numbers.rs:9-11`), and `a + b + c` is `(a + b) + c` as in JS [inferred from the
  left-associative grammar]. This matters: an analysis of the app measured, with Node, on 100,000
  random two-decimal millisecond values, that `(t - s) + s = t` fails 16,766 times and that
  `a + (b - c)` and `(a + b) - c` differ 42,082 times [reported by the port analysis]. So
  reordering float arithmetic changes behaviour, and a port must keep the source's grouping.

### 2.5 Conversions

| Function | Total? | Meaning |
|---|---|---|
| `Float.ofInt: Int -> Float`, `Float.ofNat` | total, rounds | nearest double, ties to even, like `Number(bigint)` [unverified]; ±∞ beyond the range |
| `SafeInt.toFloat`, `SafeNat.toFloat` | total, exact | every safe integer is a double |
| `Float.toInt: Float -> Option Int` | partial | `Some` if whole and finite (so not NaN, not ±∞); `-0.0` gives 0 |
| `Float.toSafeInt`, `Float.toSafeNat` | partial | `Some` if whole and within the safe bounds |
| `Float.trunc`, `floor`, `ceil`, `round` | `Float -> Float` | as JS `Math.*`; combine with `toInt` for an integer |

`round` is JS `Math.round`: halves go **up** (`-2.5` → `-2`), and `-0.3` rounds to `-0`. Rust's
`f64::round` goes away from zero (`-2.5` → `-3`) [run], [cited], so the native is written for JS
semantics (`round_ties_even` is a third rule). `Float.ofText` is left for when a program parses
text.

### 2.6 Printing

`Show Float`'s `toText` is JS `String(x)`, because a ported template `` `${t}` `` prints that:
`0.30000000000000004`, `1e+21`, `1e-7`, `NaN`, `Infinity`, and `-0` prints as `0`. Rust's `{}`
differs on four of these (`1000000000000000000000`, `0.0000001`, `inf`, `-0`) [run], so the natives
use the `ryu-js` crate, a Ryū port that follows ECMAScript's `Number::toString` and is used by the
Boa engine [cited]. `toSource` gives text that reads back as the same `Float`: `3.0` (not `3`,
which would default to `Nat`), `-0.0`, `Float.nan`, `Float.infinity` (D688).

## 3. Semantics in the kernel, the runtime and JS

### 3.1 How natives work today

`Nat` is defined as `Zero | Succ Nat` but stored as one big number, `Term::Nat` / `Value::Nat`
([checked] `crates/core/src/term.rs:89-90`, `value.rs:28-29`). Some prelude definitions have
native implementations used when their arguments are literals; the native must compute exactly
what the definition does, and the natives are trusted ([checked] `crates/core/src/native.rs:1-27`).
The runtime and the JS backend bind their own representations and operations to declarations
**by content hash**: `SafeNat` crosses as `number` only if its hash is `SAFE_NAT_HASH`; otherwise
it is an ordinary record ([checked] `crates/rt/src/natives.rs:274-305`). And the kernel already
admits **bodyless definitions** for one feature: `Delay`'s six constants are "definitions without
bodies … admitted here once their types are checked to be exactly these", with a consistency
argument that the rest of the theory has a model where they mean something ([checked]
`crates/core/src/partial.rs:1-30`).

### 3.2 The choice

A `Float` operation can't have an honest short Stitchwort definition: `+` on doubles is "add
exactly, then round to nearest-even", which needs the IEEE model. Three options:

- **(a) Fully opaque.** `Float` and all its operations are bodyless primitives. Equality and
  comparison become axioms ("`Float.same x y = True -> x = y`"), as in Rocq and F\* [cited].
- **(b) Full model now.** Define every operation over the bits, as Lean does [cited]. Correct by
  construction, but it is a software floating-point library written and checked in Stitchwort:
  far more than the port needs.
- **(c) Bits model, rounding operations bodyless (recommended, D681).** The type is the record of
  §2.2. Everything exact and short is a real definition over the bits: equality (from `Nat`'s),
  the total order, the IEEE comparisons, `neg` (flip the sign bit), `abs` (clear it), `isNaN`,
  `isFinite`. These get natives bound by hash like any other. The rounding operations (`add`,
  `sub`, `mul`, `div`, `rem`, `floor`, `ceil`, `trunc`, `round`, `ofInt`, `toInt`, `toText`) are
  bodyless primitives with a fixed type, admitted like `Delay`'s constants.

Why (c): it needs **no axioms** (equality and order are proved, not assumed), it is exactly the
shape (b) would have, so moving to (b) later replaces bodyless primitives with definitions and
changes no program, and the trusted addition is a short list of `f64` functions.

Consistency of (c) [inferred]: interpret each primitive as the IEEE function it computes, with NaN
results made the canonical NaN. That is a genuine function on valid bit patterns, so the theory
with these constants has a model, as the `Delay` argument does.

### 3.3 What the checker does with `1.5 + 2.0`

It **computes**, natively (D682). When a float primitive is applied to arguments whose `bits` are
literals, the evaluator converts the bits to `f64`, applies the Rust operation, canonicalises a NaN
result, and returns the record with the new bits as a literal. Otherwise the application is stuck
(a neutral term), and conversion compares stuck applications structurally, as it does for `Delay`.
So `0.1 + 0.2 = 0.30000000000000004` is `rfl` and a unit test on floats runs at check time.

A `Float` value in the kernel is just the record with a `Nat` literal inside; no new `Value`
variant is needed, since `Nat` is already compact. The pretty-printer shows a `Float` record with
literal bits as its literal (`1.5`), so goals stay readable.

### 3.4 Run time

- **Runtime (`crates/rt`):** a new `Value::Float(f64)`, next to `Value::Nat`/`Int`/`Text` ([checked]
  `crates/rt/src/value.rs:21-42`). The record is replaced by the `f64` when `Float`'s hash matches
  `FLOAT_DATA_HASH`; `.bits` and the record constructor become natives (`to_bits`/`from_bits`,
  canonicalising).
- **JS (`crates/js`):** a `Float` is a `number`. `+ - * / %` emit the JS operators, comparisons
  emit `=== < <=`, `round` emits `Math.round` and so on. `.bits` uses a `Float64Array`/`BigUint64Array`
  pair, canonicalising NaN.

### 3.5 Do Rust and JS agree?

| Operation | Agree? | Evidence |
|---|---|---|
| `+ - * /`, `sqrt` | yes: both IEEE 754 binary64, round to nearest-even | JS spec's Number::add etc. [unverified]; Rust: `sqrt` "guaranteed to be the rounded infinite-precision result" [cited]; `0.1 + 0.2` and `80281.87 - 80000` print identically [run] |
| `%` | yes: both truncated remainder (C `fmod`), which is exact | `5.5 % 2` = `1.5`, `-5.5 % 2` = `-1.5` in both [run]; JS spec note [unverified] |
| `floor`, `ceil`, `trunc`, `abs`, `neg` | yes: exact | Rust: "always returns the precise result" [cited] |
| `round` | **no**: JS halves up, Rust away from zero | `-2.5`: JS `-2`, Rust `-3` [run]; MDN [cited]. The native implements JS's rule |
| comparisons | yes (IEEE) | [inferred] |
| NaN bits | **no guarantee**: Rust says "nothing is guaranteed about the specific bit pattern … both payload and sign are arbitrary" [cited]; WebAssembly (the playground) leaves NaN bits nondeterministic [cited]; x86 produces a negative NaN for `0/0` [unverified] | canonicalise every NaN result in the kernel, the runtime's `.bits`, and JS's `.bits`. JS can only see NaN bits through typed arrays |
| `-0` printing | differs (`-0` vs `0`) | [run]; fixed by `ryu-js` (§2.6) |
| literal parsing | agree on tested strings | [run]; correctly rounded in both [unverified], tested in §7 |
| `pow`, `exp`, `log`, trig | **no**: Rust: "precision … is non-deterministic" [cited]; JS engines differ [unverified] | **excluded** from stage 1 |

`sqrt` and `min`/`max` (JS rules for NaN and ±0) are exact too, but the app doesn't need them; they
can join later without a decision.

**One more trap:** the runtime's optimiser must not simplify `Float` arithmetic algebraically
(`x + 0 → x` is wrong for `x = -0.0`). `crates/rt/src/opt.rs` does constant propagation and beta
only ([checked] `opt.rs:1-30`), but a test pins it (§7).

## 4. Equality and ordering

Three different "equalities" are in play:

| | `NaN` vs `NaN` | `0.0` vs `-0.0` | Lawful? |
|---|---|---|---|
| JS `===` (IEEE) | not equal | equal | not reflexive; not a congruence (`1/0 ≠ 1/-0`) |
| JS `Object.is` (same bits) | equal | not equal | yes |
| Stitchwort `x = y` | equal | not equal | yes: it's `Object.is`, from §2.2 |

Today `a == b` is "the `DecEq` instance's decision of `a = b`, as a `Bool`", `a != b` is
`Not (a = b)`, and `a < b`, `a <= b` are propositions decided through `Ord` ([checked]
`numbers.rs:611-633`, `crates/syntax/src/ast.rs:554-576`). `DecEq` must decide `x = y`
([checked] `std/core/DecEq.sw:11`), so a `DecEq Float` can only be `Object.is`.

The TS app compares with `===` and `<`. A mechanical port turns `===` into `==`. If `==` were
`Object.is`, ported code would silently differ whenever a zero's sign differs, and that is not rare
for times: `Math.round(-0.3)` is `-0`, and `-0 === 0` is true in JS but `Object.is(-0, 0)` is false
[run].

**Recommendation (D683):** on `Float`, the operators are JS's:

- `a == b` is `Float.eq a b` (IEEE `===`), `a != b` is `Float.eq a b = False` as a proposition,
  `a < b` is `Float.lt a b = True`, `a <= b` is `Float.le a b = True`. So `if a < b` and
  `if a == b` do exactly what the TS did. These are definitions over the bits (§3.2), so lemmas
  such as `Float.lt a b = True -> Float.lt b a = False` are provable.
- `a = b` (the proposition), `if h: a = b`, `DecEq Float`, and derived `==` on records and data
  containing a `Float` field mean the same double (`Object.is`). TS has no structural equality, so
  the port has no derived equality to match.

The cost is that on `Float` alone, `if a == b` and `if h: a = b` can disagree (on NaN and ±0), and
the docs must say so. The alternative is to keep `==` lawful and make ported code call `Float.eq`
(Rocq's and F\*'s choice [cited]); it is more uniform but makes every port of `===` a trap.

**`DecEq` must be sound, and the port needs that.** One of the app's proved theorems uses
`Decidable.toBoolSound` on `==` of lists containing times [reported by the port analysis]: it needs
`==` on those lists to imply real equality, which only a `DecEq` deciding `x = y` gives. So derived
`==` on records and lists keeps going through `DecEq Float` (same double), and that is the case the
analysis recommends too. It differs from `===` and lodash's `isEqual` only on `0` vs `-0`, and `-0`
does reach programs from data: `JSON.parse("-0")` is `-0` [run]. A third option, SameValueZero
(NaN equal to itself, `0` equal to `-0`), would be sound only if nothing could tell `0` from `-0`,
which means removing division (`1/0` vs `1/-0`) and anything else that observes the sign; that
isn't JS's arithmetic, so it's ruled out.

**`Ord Float` (D684):** IEEE's `totalOrder` on the canonical bits: `-∞ < … < -0.0 < 0.0 < … < +∞ <
NaN`. Built with `Ord.byKey` from a key that maps the bits to an `Int` monotonically, with its
injectivity proof ([checked] `Ord.byKey` used in `Safe.sw:56-58`). This is what `sort`, `sortOn`,
`Map Float`, `Set Float` and derived `Ord` use: it is lawful, which `Ord` requires (`equal`, `flip`,
`trans`, [checked] `std/core/Ord.sw:23-40`). IEEE comparison can't be an `Ord`: `equal` fails for
`0.0`/`-0.0` (they compare equal but aren't the same double) and NaN breaks `flip` (NaN is neither
less, equal nor greater). Lodash's sort isn't a total order either: it puts NaN last but
`compareAscending(NaN, NaN)` is 1 both ways [reported by the port analysis]. So the `<` operator
does not go through `Ord` (above), and `Float` has no `Add` or `Mul` instance (§2.4): its
operators are built in, as `Nat`'s and `Int`'s are before the dictionaries exist. Splitting the
std interfaces into lawless operator interfaces and lawful ones would also work, but it changes
every existing instance and isn't needed for `Float`. Sorting times that contain no NaN and no `-0`
gives the same order either way [inferred].

## 5. The JS boundary

- **Type:** `number` in the `.d.ts`. `Option Float` is `number | undefined` (D582 already makes
  `Option T` `T | undefined`), and an optional record field.
- **Decoding (D685):** accept every finite `number`, including `-0`; refuse NaN, ±Infinity and
  anything else (`bigint`, strings), with the existing `refuse` messages. Reason: the app's data
  comes through JSON, which can't carry NaN or infinities (`JSON.stringify([NaN, Infinity])` is
  `[null,null]` [run]), so one arriving is a bug upstream, and refusing it at the edge is what
  `SafeNat` does for fractions. The port analysis recommends the same. (The app's own code refuses
  negative durations separately; that is its business, not the codec's.) The alternative is to
  accept every `number`, since `Float`'s meaning includes NaN and the infinities anyway.
- **Encoding:** the `number` itself, whatever it is: NaN and ±Infinity can arise inside
  (`0.0 / 0.0`), and the type allows them, so outputs are not checked. A refusing decoder and a
  permissive encoder is asymmetric, but each side does the honest thing for its direction.
- **Attributes** (docs/proposals/attributes.md): `Float` joins the special-codec types that reject
  `@[js.*]` attributes inside them ([checked] attributes.md:447), through the shared registry
  of D613.
- **Binding:** by content hash (`FLOAT_DATA_HASH` and one hash per primitive), as
  `SAFE_NAT_HASH` is; a test fails if `std/Float` changes without the natives being re-checked
  ([checked] the pattern at `crates/cli/tests/extract.rs:1979-1989`).

## 6. Proofs

### 6.1 What stage 1 can prove

- **Structural facts, directly about `Float` code.** The rounding operations are unknown functions
  to a proof, so anything that doesn't depend on what they compute is provable. For example: the
  times `inWindow start end xs` returns are all in `xs`, each satisfies `Float.le start t = True`,
  and they're in the same order; `shiftAll d xs` has the same length as `xs`; a sort by `Float`'s
  `Ord` returns a sorted permutation.
- **Facts about the exact operations:** `neg (neg x) = x`, `abs` is non-negative in the total
  order, `lt a b = True -> le a b = True`, `eq` is symmetric. Proved over the bits.
- **Facts about literals, by computation:** `0.1 + 0.2 = 0.30000000000000004` by `rfl`.
- **Not provable:** anything relying on what `+` computes on unknowns, e.g. `t + 0.0 = t` (false
  anyway for `t = -0.0`) or `(t - s) + s = t` (false: rounding).

### 6.2 Programs over an operations record

The port shows what proofs actually need. Every theorem proved about the app uses only the code's
own operations on times, never an arithmetic law, and they were all checked **generic** over a
record of operations with no laws, plus `DecEq` on the time types [reported by the port analysis]:

```
-- `i` is an instant, `n` a length of time. Operations only: no laws.
type TimeOps (i: Type) (n: Type) =
  { zero: n, add: i -> n -> i, sub: i -> i -> n, endTime: i -> n -> i
  , le: i -> i -> Bool, lt: i -> i -> Bool, order: i -> i -> Ordering, duration: n -> n -> n }
```

Instantiated at `Float` (built from `Float.add`, `Float.lt`, …), the theorems cover the exported
code directly. That confirms the design of §6.1: a lawless operations record is the shape, and it's
a plain record (or interface), not an extension of `Add`/`Ord`, whose laws doubles break (§4).

Where a property does need algebra (say, "re-basing times onto a new origin and back gives the
original times", false for doubles by §2.4's measurement), the laws go in a **separate hypothesis**
that only exact types can supply:

```
type TimeLaws (i: Type) (n: Type) (ops: TimeOps i n) =
  { subAdd: (t: i) -> (s: i) -> ops.add s (ops.sub t s) = t }
-- provable for ops over `Int`; no `Float` value exists
```

The theorem then shows the algorithm is right over `Int`; it says nothing about rounding. `Nat`
can't supply `subAdd` (`-` stops at zero), and `SafeInt` has no closed `add` of its own (a sum can
leave the safe range), so its operations go through `Int` [inferred].

**Don't add such a record to std yet** (D689): keep `TimeOps` in the ported module, and generalise
it into std when a second program needs one, so its shape comes from real use.

### 6.3 Later: the full model

Giving `add` and the rest definitions over the bits (Lean's route [cited]), or the
integer × 2^exponent view with exact-then-round (Flocq's [cited]), would make rounding-error
theorems possible and turn the primitives into ordinary natives. That is a library-sized project and
only worthwhile once someone needs a numerical theorem. Nothing in stage 1 blocks it.

## 7. Implementation, cost, risks, tests

### 7.1 By crate

| Crate | Work |
|---|---|
| `syntax` | `Tok::Float(text)` for `digits.digits`, `digits[.digits](e\|E)[+-]digits`; AST literal keeps text; lexer and parser tests (`x.name`, `List.map`, `xs.0`-style forms unchanged) |
| `core` | `Builtin::Float` and the primitives in the registry; admission of bodyless float primitives with exact types (new file beside `partial.rs`); evaluation rule (literal bits in, canonical bits out); hashing for primitives; pretty-printing `Float` records as literals; DESIGN.md §13 lists the new trusted functions |
| `elab` | `Kind::Float` in `numbers.rs` (forcing, whole literals, refusing inexact whole literals, IEEE `== != < <=`); `std/Float/Float.sw` (type, `isValid`, exact definitions, primitives' signatures, `DecEq`, `Ord`, `Show`, conversions) |
| `rt` | `Value::Float(f64)`; `FloatNative` table with hashes; lowering of the record, `.bits`, the constructor; `ryu-js` for `toText`; JS `Math.round` rule |
| `js` | `Boundary::Float` (`number`), codec, `.d.ts`; operators and `Math.*` calls; `.bits` via typed arrays |
| docs | `docs/syntax.md` (literals, operators on `Float`, the `==` vs `=` note), `docs/core.md`, DESIGN.md §12–13 |

### 7.2 Stages and cost

| Stage | Contents | Size (rough) |
|---|---|---|
| 1a | syntax, core primitives and evaluation, `std/Float`, `numbers.rs`, kernel tests | 900–1300 lines with tests, one lane |
| 1b | runtime and JS natives, boundary codec, `.d.ts`, differential tests | 700–1000 lines, one lane, after 1a |
| later | `sqrt`, `min`/`max`, `Float.ofText`, an operations record in std | small each, when needed |
| later | full model (§6.3) | large; its own design note |

### 7.3 Risks

- **Trusted base grows** by ~12 `f64` functions, the NaN canonicalisation and `ryu-js`. Mitigated
  by differential tests and listing them in DESIGN.md §13, as for `Nat`'s natives.
- **NaN bits** differ by platform and in WASM; every path that produces bits must canonicalise. A
  missed path would make `rfl` proofs platform-dependent.
- **`==` and `=` disagree on `Float`** (D683): a documentation and teaching cost.
- **A new kernel mechanism** (bodyless primitives that compute). Small, but it is kernel code.
- **Hash binding** means editing `std/Float` needs the natives re-checked; the existing test
  pattern catches it.

### 7.4 Acceptance tests

1. **Kernel vs runtime vs JS, bit for bit**, for each operation, on random doubles plus an edge set:
   ±0, NaN, ±∞, the smallest subnormal, `MAX_VALUE`, 2^53 ± 1, halves (`±0.5`, `±2.5`), and
   `0.49999999999999994`. JS results come from Node in the test.
2. **Literals:** 10 000 random decimal strings (plus hard cases such as `2.2250738585072011e-308`):
   elaborated bits = Node's `Number(text)` bits.
3. **Printing:** `toText` = Node's `String(x)` on the same set; `toSource` reads back to the same bits.
4. **Boundary:** `-0` and `80281.87` round-trip; NaN, ±∞, a `bigint` and a string are refused at
   decode; a NaN result encodes as `NaN`;
   `Option Float` as `undefined`.
5. **Operators:** `0.0 == -0.0` and `NaN != NaN` are true, `if h: 0.0 = -0.0` takes the else branch;
   `Math.round(-2.5)` is `-2`; `rfl : 0.1 + 0.2 = 0.30000000000000004`; `x + 0.0` is not
   simplified (stays `-0.0` + `0.0` = `0.0`).
6. **End to end:** an example module (`examples/extract/float-times.sw`) with an exported function
   over times like `80281.87`, called from a TS test, matching the same function written in TS.
7. **Rejections:** `t + n` with `n: Int`; a whole literal above 2^53 that isn't exact; `pow` absent.

## 8. Decisions

Recommendations in square brackets.

1. **D680 Name.** [`Float`, in `std/Float`] / `Number` / `F64`.
2. **D681 Model in the logic.** [(c): a record of the canonical bits; exact operations defined
   over the bits; rounding operations bodyless primitives] / (a) fully opaque with axioms /
   (b) full IEEE model now.
3. **D682 Check-time computation.** [The checker computes primitives on literals with Rust `f64`,
   canonicalising NaN, so `rfl` works on literals] / primitives never reduce.
4. **D683 Operators on `Float`.** [`== != < <=` are JS's (IEEE); `x = y`, `if h:`, `DecEq` and
   derived equality are "same double"] / `==` stays `DecEq` (same double) and ported `===`
   becomes `Float.eq a b`.
5. **D684 `Ord Float`.** [IEEE `totalOrder` with the one NaN greatest, used by sorting, maps and
   deriving] / no `Ord Float` (sort by key explicitly).
6. **D685 Boundary.** [`number`; decoding refuses NaN and ±Infinity (JSON can't carry them),
   accepts `-0`; encoding passes any `number`] / accept every `number` at decode.
7. **D686 Literals.** [`1.5`, `1e3`, `1.5e-7`, digits on both sides of `.`; nearest double; a
   decimal or exponent forces `Float`; whole literals become `Float` in a `Float` group, refused if
   not exact] / also refuse inexact decimals (impossible in practice: `80281.87` isn't exact) /
   no exponent form.
8. **D687 Stage-1 operations.** [`+ - * / %` (no divisor proof), `neg`, `abs`, `floor`, `ceil`,
   `trunc`, `round` (JS rules), `isNaN`, `isFinite`, conversions of §2.5; no `pow` or
   transcendental functions] / also `sqrt`, `min`, `max` now.
9. **D688 Printing.** [`toText` = JS `String(x)` via `ryu-js`; `toSource` re-readable (`3.0`,
   `Float.nan`)] / Rust's formatting.
10. **D689 Operations record for proofs.** [Not in std yet: keep the lawless `TimeOps` record in
    the ported module, with laws as a separate hypothesis for exact types; std when a
    second program needs it] / add a generic operations record and a laws record to std in stage 1.

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
