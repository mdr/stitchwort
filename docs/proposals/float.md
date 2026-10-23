# Proposal: `Float`, a JavaScript number

**Status:** draft 2, 23 October 2026. Design-review gate: nothing is implemented. Follows D645 (a
JS-number `Float`). Draft 1's decisions D680 to D689 keep their numbers; this draft adopts every
correction and recommendation of an external review (D696), which flips D683 and D685. New
decisions start at D701 ([§8](#8-decisions)). Written against commit `5f26aacf`.

Labels: **[checked]** (read in this repository, `file:line`), **[reported by the port
analysis]** (measured or checked by a separate analysis of the motivating app, not re-run here),
**[run]** (run while writing this: Node 22.23.3 and rustc 1.99.0 on macOS/arm64; the snippets are
in [Appendix A](#appendix-a-snippets-run)), **[cited]** (read in the source linked in
[Sources](#sources)), **[cited by the review]** (the reviewer quotes or summarises a specification;
not re-read here), **[inferred]** (my reading, not stated anywhere), **[unverified]** (from
memory, not re-checked).

## Response to review (draft 2)

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
  can be reasoned about. The rounding operations (`+ - * / %`, `floor`, `round`, `ofInt`) are
  **bodyless primitives**: the checker computes them with Rust `f64` when their arguments are known
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
def Float.neg (x: Float): Float :=
  if Float.isNaN x then Float.nan
  else Float.flipSign x   -- bits ± 2^63, with its `valid` proof
```

(`flipSign` is illustrative: it adds or subtracts 2^63 and proves the result is still valid,
which needs `isNaN x = False`.)
`neg (neg x) = x` still holds: for NaN both sides are `Float.nan`, otherwise the flip is an
involution that keeps `isNaN` false [inferred; to be proved in stage 1a]. `abs` (clear the sign
bit) is closed already, since the canonical NaN's sign bit is clear [inferred].

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
| `1e400` | **refused** (recommended): "too large for a `Float`; use `Float.infinity`" | JS and Rust give `Infinity` [run]. Turning a literal into infinity is a much larger change than rounding, and a program that means infinity can say so |
| `1e-400` | **refused** (recommended): "too small for a `Float`: it would be `0.0`" | JS and Rust give `0`, and `-1e-400` gives `-0` [run]. Losing every digit is not rounding in the usual sense. Literals that land on a subnormal (`5e-324`) are accepted |

The alternative for the last two is to accept them as JS does. I recommend refusing because no
ported program needs either, and both read as mistakes; it's a one-line change later.

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

Today a group of `+ - * / %` and comparisons gets one operand type, decided in order by the
expected type, a prefix `-` (forcing `Int`), the leaves, and a default of `Nat` ([checked]
`crates/elab/src/numbers.rs:5-11`, steps 1, 2 and 5 at `numbers.rs:441`, `468`, `523`). Add `Kind::Float`:

- **Step 1 (the expected type)** can now decide `Float`.
- **New step 1b, before minus signs:** a decimal or exponent literal forces `Float`. So a `-`
  in the same group is `Float.neg` or `Float.sub`, not a reason for `Int`.
- **A whole literal in a `Float` group is a `Float`** (exactly, or refused as above).
- **A negative literal `-k` at `Float` is `Float.neg (k as Float)`**, so `-0` is `-0.0`, as in JS.
  (At `Int`, `-0` is `OfNat 0`, [checked] `numbers.rs:98-100`; that stays.)
- **No mixing:** `t + n` with `t: Float`, `n: Int` is the existing mismatch error; the fix is
  `t + Float.ofInt n`.

| Expression | Type | Value | Why |
|---|---|---|---|
| `-1 + 0.5` | `Float` | `-0.5` | step 1b decides `Float` before the minus can force `Int` |
| `0.5 + -1` | `Float` | `-0.5` | same group; `-1` is `Float.neg 1.0` |
| `def x: Float := -0` | `Float` | `-0.0` (bits `0x8000000000000000`) | expected type, then `Float.neg 0.0` |
| `-0` alone | `Int` | `0` | unchanged |
| `t - 1000` (`t: Float`) | `Float` | | the leaf decides; `1000` is exact |
| `1.5 * n` (`n: Nat`) | error | | `Float` vs `Nat` mismatch; write `Float.ofNat n` |

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
| `Float.toInt` | `Float -> Option Int` | `Some` of the integer the double represents when it is finite and whole, else `None`. Total, like every function; the `Option` is the checked result. **An ordinary definition over the bits**, with a native |
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
follows ECMAScript's `Number::toString`, as used by the Boa engine [cited]. `toSource` gives text
that reads back as the same `Float`: `3.0` (not `3`, which would default to `Nat`), `-0.0`,
`Float.nan`, `Float.infinity`. The two stay separate.

**`toText` does not reduce in the kernel in stage 1** (§3.6 explains why). It is a bodyless
primitive with no reduction rule, so `Float.toText 0.5 = "0.5"` is not provable by `rfl`, and the
kernel evaluator that runs `test` declarations ([checked] `crates/driver/src/driver.rs:899`) gets
stuck on it: a Stitchwort test that compares printed floats can't be written in stage 1. Tests of
printing are Rust and Node tests (§7.4). `stitchwort run` uses the Rust runtime ([checked]
`crates/driver/src/run.rs:328-332`), so programs still print floats.

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
zero, and map every NaN to the canonical NaN. For each operation `op`, with `modelOp` the kernel's
meaning (the reduction rule, or the definition over the bits):

> α(runtimeOp(x, y)) = modelOp(α x, α y)

for the kernel evaluator (native and WASM builds), the Rust runtime and the generated JS. It
governs arithmetic, the record constructor and `.bits`, `DecEq`, `Ord`, the IEEE comparisons,
hashing of values, and constant folding. §7.4 tests it, path by path.

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
   over the bits (`DecEq`, `Ord`, `toInt`) are ordinary natives and do switch off.

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
  value and `rfl` proves them equal. Without definitional proof irrelevance, a *different* proof
  in `valid` would make the records only propositionally equal (the `SafeNat.mkExt` pattern,
  [checked] `crates/elab/src/std/Int/Safe.sw:26-30`), so using one witness everywhere matters
  [inferred]. A debug assertion and a test evaluate `isValid` on every result.

A `Float` value in the kernel is just the record with a `Nat` literal inside; no new `Value`
variant is needed. The pretty-printer shows a `Float` record with literal bits as its literal
(`1.5`), so goals stay readable.

### 3.5 Run time and the representation invariant (D701)

The review asks for one of two run-time invariants: (1) every stored `Float` is physically
canonical; (2) values may hold any NaN, and every representation-sensitive operation handles them
canonically. The recommendation is **(1) wherever Stitchwort owns the representation, which leaves
JS with a one-item audit**:

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
  arrays [inferred]; `===`, `<`, `Object.is`, `Map`, `Set` and `String` treat all NaNs alike
  (`Object.is` of a negative-payload NaN and `NaN` is true, and the payload survives `* 1` in
  Node) [run]. So JS is invariant (2) with exactly one representation-sensitive operation in
  generated code, `.bits` (a `Float64Array`/`BigUint64Array` pair), which canonicalises. The audit
  list for JS: `.bits`; lawful `DecEq` (lowered to `Object.is`, NaN-blind); `Ord` (lowered via the
  canonical `.bits` key, or written NaN-first); value hashing if the JS backend ever hashes. A test
  forbids typed arrays anywhere else in the runtime prelude.

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

**On `toText` (D688):** the review's three options are to test and specify supported engines, to
use one formatting algorithm everywhere (so JS would call a Stitchwort formatter, not `String(x)`),
or to keep `toText` from reducing in the kernel. The recommendation is the third for stage 1: the
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
`Float.ieeeLt b a` and `a >= b` as `Float.ieeeLe b a`. Not `!Float.ieeeLt a b` for `>=`: with NaN,
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
  (`bigint`, strings), with the existing `refuse` messages. NaN is decoded to the canonical NaN.
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
checked `number` as `SafeNat` does. Recommended: no `FiniteFloat` in stage 1. The port validates
at its own types; `FiniteFloat` joins std when a program wants the check at the boundary, so its
shape comes from use.

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
- **Facts about the exact definitions:** `neg (neg x) = x`, `abs` is non-negative in the total
  order, `ieeeLt a b = True -> ieeeLe a b = True`, `ieeeEq` is symmetric, `toInt` round-trips
  through `ofInt` on whole doubles.
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
4. **Differential tests transport bits.** Compare results by their exact binary64 bits (hex) or
   another lossless encoding, not through JSON or `===`, which hide `-0` vs `0` and turn NaN and
   ±Infinity into `null`. Include signed-zero equality branches, duplicate times, stability and
   internally produced non-finite values.

These are open obligations for each port, not evidence that a port is wrong.

## 7. Implementation, cost, risks, tests

### 7.1 By crate

| Crate | Work |
|---|---|
| `syntax` | `Tok::Float(text)`; no `Float` token right after `.`; AST literal keeps text; lexer and parser tests (`x.name`, `List.map`, `xs.0.1`, `[x, ..rest]` unchanged) |
| `core` | admission of bodyless float primitives with exact types and names (beside `partial.rs`); the reduction rule (forced arguments, canonical bits out, the standard witness), always on; `FLOAT_CONTRACT` in primitive hashes; pretty-printing `Float` records as literals; DESIGN.md §13 lists the new trusted rules |
| `driver` | `build.rs`: rustc version and target in `FINGERPRINT` |
| `elab` | `Kind::Float` in `numbers.rs` (step 1b, whole literals, refusals, negative literals at `Float`); `std/Float/Float.sw` (type, `isValid`, `neg`/`abs`/`isNaN`/`isFinite`, `ieeeEq`/`ieeeLt`/`ieeeLe`, `toInt`, primitives' signatures, `DecEq`, `Ord`, `Show`, conversions) and their proofs |
| `rt` | `Value::Float(f64)` with the canonicalising constructor; `FloatNative` table bound by hash; lowering of the record, `.bits`, the constructor; `ryu-js` for `toText`; JS `Math.round` rule |
| `js` | `Boundary::Float` (`number`, all values), codec, `.d.ts`; operators and `Math.*` calls; `Object.is` for `DecEq`, `===` for `ieeeEq`; literals from bits; `.bits` via typed arrays |
| docs | `docs/syntax.md` (literals, `Float` operators, `ieeeEq` and porting `===`), `docs/core.md`, DESIGN.md §12–13 |

### 7.2 Stages and cost

| Stage | Contents | Code size (guess) |
|---|---|---|
| 1a | **The thin end-to-end slice**: the representation and its invariant, constructor and `.bits` in all three evaluators, `neg`, `add`, `DecEq` and `ieeeEq`, decimal literals, the boundary codec, the trust contract's plumbing (hash tags, `FLOAT_CONTRACT`, fingerprint), and the four-path differential test for those | 800–1200 lines with tests |
| 1b | the rest of D687's operations, `Ord Float`, `ieeeLt`/`ieeeLe`, `toInt`, `round`, conversions, printing, the full test table | 900–1300 lines |
| later | `sqrt`, `min`/`max`, `Float.ofText`, `FiniteFloat`, an operations record in std | small each, when needed |
| later | full model (§6.3) | large; its own design note |

The line counts are code-size guesses. **The main uncertainty is not code size** but (1) how hard
the proofs over the bits are (the `valid` obligations of `neg` and friends, `Ord.byKey`'s
injectivity for the total-order key, `toInt` against `ofInt`), which may need `Nat` bit lemmas that
don't exist yet; and (2) getting the trusted computation to agree across the four execution paths,
which 1a is designed to expose early.

### 7.3 Risks

- **Trusted base grows** by ~11 reduction rules and the NaN canonicalisation (`toInt` is no longer
  one; `toText` doesn't reduce in the kernel). Mitigated by the contract (§3.3), the differential
  tests and listing them in DESIGN.md §13.
- **NaN bits** differ by platform and in WASM; D701 makes the Rust runtime canonical by
  construction and leaves JS one audited site.
- **Porting `===` and `<` is manual** (D683): a port that writes `==` for `===` compiles and
  differs on `-0` and NaN. Mitigated by §6.4's audit, and docs.
- **A new kernel mechanism** (bodyless primitives that compute). Small, but it is kernel code.
- **Hash binding**: editing `std/Float` needs the natives re-checked; the existing test pattern
  catches it.

### 7.4 Acceptance tests

From draft 1, kept:

1. **Bit for bit** for each operation on random doubles plus an edge set: ±0, NaN, ±∞, the smallest
   subnormal, `MAX_VALUE`, 2^53 ± 1, halves (`±0.5`, `±2.5`), `0.49999999999999994`,
   `4503599627370497`. JS results come from Node in the test.
2. **Literals:** 10,000 random decimal strings (plus hard cases such as
   `2.2250738585072011e-308`): elaborated bits = Node's `Number(text)` bits; the §2.3 table's
   refusals and `9007199254740994`; `-1 + 0.5`, `0.5 + -1`, `def x: Float := -0` (bits
   `0x8000000000000000`).
3. **Printing:** the Rust runtime's `toText` = Node's `String(x)` on the same set; `toSource`
   reads back to the same bits.
4. **Boundary:** `-0`, `80281.87`, NaN, ±Infinity round-trip (`Object.is`); a `bigint` and a
   string are refused; `identity (makeInfinity ())` works through the exports; `Option Float` as
   `undefined`.
5. **Operators:** `0.0 == -0.0` is `False`, `Float.nan == Float.nan` is `True`,
   `Float.ieeeEq 0.0 (-0.0)` is `True`, `Float.ieeeEq Float.nan Float.nan` is `False`; `-0.0 < 0.0`
   holds; `Math.round` cases of §2.5; `rfl : 0.1 + 0.2 = 0.30000000000000004`; `x + 0.0` is not
   simplified.
6. **End to end:** `examples/extract/float-times.sw`, an exported function over times like
   `80281.87`, called from a TS test, matching the same function written in TS, compared by bits.
7. **Rejections:** `t + n` with `n: Int`; `9007199254740993`, `1e400`, `1e-400` as `Float`;
   `pow` absent; `xs.0.1`.

Added from the review:

| Area | Requirement |
|---|---|
| Execution paths | Compare the native kernel, the WASM kernel, the native runtime and generated JS explicitly, for every operation |
| NaN abstraction | Several NaN signs and payloads (made with typed arrays in JS, `from_bits` in Rust) through `.bits`, `DecEq`, `Ord`, and hashing: all give the canonical result |
| Binary operations | All pairs from the edge set, including signed zeros, subnormals, infinities and extreme magnitudes |
| Representation lowering | Constructor and `.bits` through generic functions and derived `DecEq` on records with `Float` fields |
| Operator resolution | After inlining and specialisation, `==` and `Float.ieeeEq` (and `<` vs `ieeeLt`) stay distinct (§4.4) |
| Conversions | `toInt` on large whole doubles (`1e100`, `MAX_VALUE`), huge positive and negative integers through `ofInt`, halfway cases, the overflow thresholds |
| Optimisation | Folded vs run-time results agree; no reassociation, no FMA contraction (an `a * b + c` case whose fused result differs) |
| Port behaviour | Signed-zero equality branches, duplicate timestamps, sort stability, internally produced non-finite values |
| Test transport | Exchange hex bit patterns (or another lossless encoding), never JSON numbers, including in the app's own differential test |
| Contract plumbing | Two float primitives of the same type hash differently; bumping `FLOAT_CONTRACT` changes their hashes; the fingerprint changes with the rustc version |

## 8. Decisions

Recommendations in square brackets. D680–D689 keep draft 1's numbers; changes are marked.

1. **D680 Name.** `Float`, in `std/Float`. *Decided.*
2. **D681 Model in the logic.** [(c): a record of the canonical bits; exact operations defined
   over the bits; rounding operations bodyless primitives] / (a) fully opaque / (b) full model now.
   *Approved by the review. Changed:* `neg` has an explicit NaN case; the representation
   invariant is stated (§2.2); `toInt` moves from primitive to definition.
3. **D682 Check-time computation.** [The checker computes primitives on known doubles, under the
   trust contract of §3.3: the commuting equation, conditions C1–C6, reduction on values, primitive
   names and `FLOAT_CONTRACT` in hashes, rustc and target in the fingerprint, always on] /
   primitives never reduce. *Approved by the review, with the contract added.*
4. **D683 Operators on `Float`.** *Flipped.* [`== != < <=` keep their lawful meanings (`DecEq`,
   `Ord Float`); JS's `===`, `<`, `<=` are `Float.ieeeEq`, `Float.ieeeLt`, `Float.ieeeLe` in ported
   code; compilation keeps them distinct] / draft 1's IEEE operators on `Float`.
5. **D684 `Ord Float`.** [IEEE `totalOrder`, one NaN greatest, used by `<`, sorting, maps and
   deriving] / no `Ord Float`. *Approved; added:* ports keep their comparator and stability
   (§6.4); native JS `Map`/`Set` lowering would need canonical-bit keys.
6. **D685 Boundary.** *Flipped.* [`number`; decoding accepts every `number`, NaN and ±Infinity
   included, NaN made canonical; encoding passes the value] / draft 1's refusal of NaN and
   ±Infinity on input.
7. **D686 Literals.** [`1.5`, `1e3`, `1.5e-7`; correctly rounded; elaborated to bits once, hashed
   as bits, JS generated from the bits; a decimal or exponent forces `Float` before a minus forces
   `Int`; `-k` at `Float` is `Float.neg`, so `-0` is `-0.0`; whole literals exact or refused; no
   `Float` token right after `.`] / no exponent form. *Approved, made explicit.* **New
   sub-choice:** [refuse literals that overflow to ±∞ (`1e400`) or underflow to ±0 (`1e-400`)] /
   accept them as JS does.
8. **D687 Stage-1 operations.** [`+ - * / %` (no divisor proof), `neg`, `abs`, `floor`, `ceil`,
   `trunc`, `round` (the full JS rule), `isNaN`, `isFinite`, `ieeeEq`/`ieeeLt`/`ieeeLe`, the
   conversions of §2.5 with `toInt` as a definition over the full range; no `pow` or
   transcendental functions] / also `sqrt`, `min`, `max` now. *Approved; changed:* `toInt` is a
   definition, `round` is specified in full.
9. **D688 Printing.** [`toText` = JS `String(x)` at run time via `ryu-js`; it does **not** reduce in
   the kernel in stage 1, so no exact string proofs and no Stitchwort tests of printed floats;
   `toSource` re-readable] / specify and test supported engines' `Number::toString`, then let the
   kernel reduce it / one Stitchwort formatter on every backend. *Changed:* the kernel no longer
   computes `toText`.
10. **D689 Operations record for proofs.** [Not in std yet: `TimeOps` stays in the ported module,
    laws as a separate hypothesis] / a generic record in std now. *Approved;* the `TimeLaws`
    comment names `ieeeTimeOps`.
11. **D701 Run-time representation invariant (new).** [Physically canonical in the kernel and the
    Rust runtime (one canonicalising constructor); in JS, NaN-agnostic values with `.bits` the one
    canonicalising, representation-sensitive operation, and no typed arrays elsewhere] / arbitrary
    NaNs everywhere with every representation-sensitive operation audited / canonicalise every JS
    result too.
12. **D702 Finiteness (new).** [Stage 1 has no `FiniteFloat`: the port checks finiteness in its own
    types; `FiniteFloat`, a checked `number` like `SafeNat`, joins std when a program wants the
    check at the boundary] / add `FiniteFloat` in stage 1.

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
