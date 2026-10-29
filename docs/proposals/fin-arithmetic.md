# Proposal: wrapping arithmetic, on `Fin n` or beside it

**Status:** Draft 1, 21 October 2026. **Built:** `Mod n` is in the library (`Std.Mod`, `examples/accept/mod-arith.sw`; [syntax.md](../syntax.md)), with `Fin` unchanged, as recommended; the note below is the design. It
answers D310, Matt's question "Could we make our `Fin n` type have wrapping
behaviour?", meaning `+`, `-` and `*` modulo `n`, as Lean's `Fin 100` has them
(four Lean solutions to Advent of Code 2025 day 1 used `(50 : Fin 100) + x`, so
the dial needed no `% 100`: [aoc-day01-community.md §3.2](../comparisons/aoc-day01-community.md)).

Claims about Stitchwort were checked at commit `e1f1b69`. Labels:

- **[checked: S]**: read in S (a file in this repository, or a URL);
- **[run]**: a program run with the release CLI on 21 October 2026, in a
  scratch directory outside the repository;
- **[inferred]**: my reasoning from checked facts;
- **[unverified]**: believed, not confirmed.

## 0. Summary

**Short answer: not on `Fin` itself, and not just by adding instances. Add a
separate type, `Mod n`, for numbers that wrap, and keep `Fin n` as the type of
positions in a `Vec`.**

Three things stand in the way of Lean's `(50 : Fin 100) + x` today, whatever
`Fin` looks like inside:

1. **`+` needs a zero, and `Fin 0` has no values.** `+` means `Add.add`, and
   an `Add` instance must give `zero` ([checked: `std/core.sw`, `interface
   Add`]). An instance can't be for `Fin (Succ n)` only (`E-INSTANCE-HEAD`:
   "an instance must be for a type name applied to distinct variables"), nor
   ask for `[auto ok: n != 0]` (`E-INSTANCE-CONTEXT`) **[run]**. Lean gets
   round this with a `NeZero n` class; Stitchwort would need a change to its
   instance rules.
2. **Number literals are `Nat` or `Int` only.** `def x: Fin 100 := 50` is
   refused: "a numeral can only be the prelude's `Nat` or `Int`" **[run]**.
   That was decided (D165, no generic literals:
   [interfaces.md §5.13](interfaces.md)).
3. **`-` has no interface.** `-`, `/` and `%` are `Nat`/`Int` only
   ([checked: interfaces.md §5.13 table]).

And there's a reason not to want it on `Fin`: Lean's own community has been
moving wrap-around *away* from `Fin`. Mathlib took the ring and `Nat`-cast
instances on `Fin n` out of global scope because a comparison `x < n` could be
"silently introducing wraparound arithmetic"
([mathlib4 PR #25476](https://github.com/leanprover-community/mathlib4/pull/25476)),
and keeps modular arithmetic in a separate type, `ZMod n`. Agda, Idris (for
literals), mathcomp, Dafny and F* all keep wrapping off the index type or make
it explicit (§2).

**Recommendation.** A new library type `Mod n` (in `std/Mod/Mod.sw`): a record
of a `Nat` and a proof that it is in range, with `+` and `*` that wrap (its
`Add` and `Mul` instances, laws proved), `==` and `<` derived, `Mod.sub`,
`Mod.neg`, `Mod.ofNat` and `Mod.ofInt` (both wrap), and conversions to and from
`Fin`. `Mod 0` has one value, 0 (as mathcomp's `'Z_p` is "mod `max p 2`"), so
every `Mod n` has a zero and the instances need no language change. `Fin` and
`Vec` don't change. A prototype with the `Add` instance and its three laws
checks today, and day 1 part 1 written with it passes the example **[run]**
(§6).

## 1. What `Fin` is today, and what a wrapping `+` would need

`Fin n` is the Agda/Idris family ([checked: `std/Fin/Fin.sw`]):

```
type Fin: Nat -> Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)
```

The number 3 is `FSucc (FSucc (FSucc FZero))`. Its job is to be a position in
a `Vec a n`, so that `Vec.get: Vec a n -> Fin n -> a` needs no bound proof:
the type of the index is the proof. `Vec.get` and its lemmas (`getMap`,
`getReplicate`, `getZipWith`, `ext`, ...) recurse on `FSucc`
[checked: `std/Vec/Vec.sw`]. It has `toNat`, `ofNatLt`, `ofNat [auto i < n]`,
`Show`, `DecEq` and `Ord`, and no arithmetic. It's used 76 times, mostly in
the library and examples; in AoC only by day 4's parse proof
(`Aoc/Year2025/Day04/Proofs/Parse.sw`, through `Fin.ofNatLt` and `Fin.toNatOfNatLt`).

**Interfaces.** `+` and `*` mean `Add.add` and `Mul.mul` for every type, and
the instances carry laws [checked: `std/core.sw`, D187]:

| Interface | Fields |
|---|---|
| `Add` | `zero`, `add`, `zeroAdd: add zero x = x`, `assoc`, `comm` |
| `Mul` | `one`, `mul`, `oneMul`, `mulOne`, `assoc` |

For wrapping `+` these laws are true modulo `n`, and the library already has
the lemmas they need: `Nat.modAddMod: (a % d + b) % d = (a + b) % d`,
`Nat.addModMod`, `Nat.modSmall`, `Nat.modLt` [checked: `std/Nat/Arith.sw`].
For `*` it lacks the matching `Nat.modMulMod`/`Nat.mulModMod` (about three new
lemmas) [checked: no such names in `std/`].

**Two ways to store a number below `n`:**

| | Inductive (today) | Record (Lean's `Fin`, our `Dial`) |
|---|---|---|
| Definition | `FZero` / `FSucc` | `{ value: Nat, isLt: value < n }` |
| 3 is | three `FSucc`s around `FZero` | `{ value = 3, isLt = … }` |
| Cost of a number k | k cells, at run time and when checking | one native number; the proof is erased at run time |
| `Vec.get` | matches `FZero`/`FSucc`, no proof | needs a lemma to step from `i + 1` to `i` |
| In JS | nested `{ tag: "FSucc", … }` objects; families can't cross the export boundary (`E-EXPORT`) [checked: docs/core.md "JS"; indexed-families.md test 28] | `{ value: 3n }` (proof fields are erased) [checked: docs/core.md "JS"] |

Measured cost of the inductive form, by `rfl` on
`Fin.toNat (Fin.ofNat k: Fin (k+1)) = k` **[run]**: 0.10 s for k = 9,999,
1.3 s and 1.1 GB of memory for k = 999,999. Every wrapping operation through
`toNat`, `%` and `ofNatLt` would walk and rebuild that chain: O(n) per `+`.
Idris's `Data.Fin` warns about the same thing: arithmetic on `Fin` is
"exceedingly inefficient at run time"
([Idris2 `Data/Fin.idr`](https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Data/Fin.idr)).

## 2. What other languages do

Fuller table, with sources: [Appendix A](#appendix-a-other-languages).

**Lean 4 core** wraps on `Fin` itself. `Fin n` is a structure `{ val, isLt }`;
`+`, `*` are `(a + b) % n`, `(a * b) % n`, and `-` is `((n - b) + a) % n`
(written that way round for speed of checking, per a comment in the source);
literals wrap too, through `OfNat (Fin n) i` given `[NeZero n]`, so
`(2 : Fin 3) + (2 : Fin 3) = 1`
([Init/Data/Fin/Basic.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Data/Fin/Basic.lean),
[reference](https://lean-lang.org/doc/reference/latest/Basic-Types/Finite-Natural-Numbers/)).
The reasons given, in a 2022 Zulip thread asking for a `Fin` without
wrapping: Lean 3 did it, it's "how numbers mod n work in mathematics", and
functions must be total. The thread ended without a change
([Zulip: "Fin without wrapping"](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Fin.20without.20wrapping.html)).
Lean doesn't *index* with `Fin` arithmetic: `Array` and `Vector` take a `Nat`
and a proof `i < size`, found by a tactic
([Init/GetElem.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/GetElem.lean)).
`UInt8` … `UInt64` wrap, and are built on `BitVec`, which is built on `Fin`.

**Mathlib** keeps modular arithmetic in `ZMod n` (`ZMod 0` is `ℤ`,
`ZMod (n+1)` is `Fin (n+1)`), and made `Fin`'s ring and `Nat`-cast instances
opt-in (`open Fin.CommRing`) because of silent wrap-around
([PR #25476](https://github.com/leanprover-community/mathlib4/pull/25476),
[ZMod/Defs.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Data/ZMod/Defs.lean)).
Earlier, Reid Barton: "I don't think you're supposed to use `+` on `fin n`
— but it exists in order to make numerals work … there's another type for
that"
([Zulip, 2020](https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Comm.20ring.20for.20.60fin.20n.60.html)).

**Agda** never wraps on `Fin`: `_+_ : Fin m → Fin n → Fin (toℕ i + n)` widens
the bound, `_-_` needs a proof that it doesn't go below zero, and wrapping is
an explicit `_mod_ : ℕ → (d : ℕ) → {NonZero d} → Fin d`
([Data/Fin/Base.agda](https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Data/Fin/Base.agda),
[Data/Nat/DivMod.agda](https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Data/Nat/DivMod.agda)).

**Idris 2** has both: a wrapping `Num (Fin (S n))` (note the `S n`: no
instance for `Fin 0`), but literals must be proved in range at compile time,
and `Data.Fin.Arith` has widening, non-wrapping `+` and `*`
([Data/Fin.idr](https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Data/Fin.idr),
[Data/Fin/Arith.idr](https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Data/Fin/Arith.idr)).

**Rocq/mathcomp**: the index type `'I_n` (a `nat` and a proof) has named
wrapping functions `Zp_add`, `Zp_mul`, `Zp_opp`; the ring structure is on
`'Z_p`, defined as the integers modulo `max p 2` so that it is "always a
proper ring"
([fintype.v](https://raw.githubusercontent.com/math-comp/math-comp/master/boot/fintype.v),
[zmodp.v](https://raw.githubusercontent.com/math-comp/math-comp/master/algebra/zmodp.v)).

**Haskell** `finite-typelits`: `Finite n`'s `+ - *` wrap, but an
out-of-range literal is a run-time error; non-wrapping `add`, `sub`,
`multiply` exist beside them
([Data/Finite](https://hackage.haskell.org/package/finite-typelits/docs/Data-Finite.html)).
`modular-arithmetic`'s `Mod i n` is a separate type for modular numbers
([Data.Modular](https://hackage.haskell.org/package/modular-arithmetic/docs/Data-Modular.html)).

**Machine integers and verifiers.** Go and C's unsigned types wrap by
definition. Rust's `+` is checked in debug builds and wrapping is explicit
(`wrapping_add`, `Wrapping<T>`), because wrap-around is rarely what's meant
([RFC 560](https://raw.githubusercontent.com/rust-lang/rfcs/master/text/0560-integer-overflow.md)).
Zig makes overflow on `+` illegal and spells wrapping `+%` and saturating `+|`
([Zig docs](https://ziglang.org/documentation/master/)). Dafny's bounded
`newtype`s give a proof obligation when a result leaves the range, while its
`bv8` types wrap; F*'s `UInt32.add` requires no overflow and `add_mod` wraps
([Dafny reference](https://dafny.org/latest/DafnyRef/DafnyRef),
[FStar.UInt32.fsti](https://raw.githubusercontent.com/FStarLang/FStar/master/ulib/FStar.UInt32.fsti)).

**The pattern.** Only Lean core (and Haskell's `Finite`) put wrapping `+` on
the bounded-index type by default, and Lean's library ecosystem has since
fenced it in. Everyone else either keeps index arithmetic honest (widen, or
ask for a proof) and puts modular arithmetic in a separate type, or makes
wrapping an explicit, differently-named operation.

## 3. The worry: wrapping on an index type

With wrapping `+` on the type that indexes vectors, `i + 1` at the last
position is position 0. A loop "to the next cell" that should stop at the
edge silently wraps to the other side of the grid instead, and the types
can't catch it, because the result is a perfectly good `Fin n`. That's the
bug Mathlib's PR describes ("silently introducing wraparound arithmetic"),
there caused by a coercion making `x < n` mean `x < (n : Fin k)`. Stitchwort
has no coercions, so that exact path doesn't exist here [inferred], but the
plain `i + 1` case does.

A dial and an index want opposite things from `+`: a dial wants to wrap, an
index wants to be stopped (or proved not to need stopping). One type can't
default to both. Two types, with explicit conversions, can.

## 4. Options

| | Option | `+` on `Fin`? | Language changes | Cost |
|---|---|---|---|---|
| 1 | Keep inductive `Fin`; add wrapping `Add`/`Mul` instances via `toNat`, `%`, `ofNatLt` | yes | instance rules (a zero for `Fin 0`, see below) | O(n) per operation; laws modulo `n` |
| 2 | Rebuild `Fin` as a record (Lean's), with wrapping `+ - *` | yes | instance rules; and for Lean's literals, generic literals and a `Sub` interface | rewrite `Vec.get` and its lemmas; day 4's parse proof; the footgun |
| 3 | **Keep `Fin` for indices; add `Mod n` for numbers that wrap** | no | none | one new library file |
| 4 | Explicit operators on `Fin` (Zig's `+%`), or named `Fin.addWrap` | `+%` only | new operator syntax (for `+%`) | O(n) on the inductive form |
| 5 | "Checked" `+`: `Fin.addChecked: Fin n -> Fin n -> Option (Fin n)`, or Agda's widening `Fin m -> Fin n -> Fin (m + n)` | no | none | not wrapping, so it doesn't answer D310; useful later for indices |

**Options 1 and 2 hit the same wall: the zero.** `Add (Fin n)` must produce
a `zero: Fin n` for every `n`, and `Fin 0` has no values. The ways round it
are all language changes:

- allow instance heads like `Add (Fin (Succ n))` (Idris's `Num (Fin (S n))`).
  Today that's `E-INSTANCE-HEAD` **[run]**, which exists so that two
  instances overlap exactly when they name the same type;
- allow an instance to ask for a proof, `[auto ok: n != 0]` (Lean's
  `[NeZero n]`). Today that's `E-INSTANCE-CONTEXT` **[run]**, which exists so
  that instance search always ends. An `auto` proof doesn't start another
  instance search, so it wouldn't threaten that [inferred], but it is a
  change to the interface rules, and `Fin.ofNat 50: Fin 100` would then have
  to decide `100 != 0` during instance resolution.

Option 3 avoids the wall by choosing what `Mod 0` means (§5.2).

**Option 4.** A Zig-style `+%` is new syntax for one library type. Named
functions (`Fin.addWrap`) need nothing new but inherit the O(n) cost, and add
little once `Mod` exists: `(i.toMod + j.toMod).toFin` says the same thing.

**Option 5** is the right shape for *index* arithmetic when a program needs
it (as Agda and Idris's `Data.Fin.Arith` do), but nothing needs it yet.

## 5. Design dimensions for `Mod n`

### 5.1 Representation and speed

A record, as `Dial` already is (`type Dial (highest: Nat) = { position: Nat,
inRange: position <= highest }`, [checked: `Aoc/Year2025/Day01/Day01.sw`]): a native
number plus a proof that is erased at run time [checked: docs/core.md,
"Running a program"]. Arithmetic is native `Nat` arithmetic and one `%`.

**One measured trap, and its fix.** The checker evaluates the proof inside a
record value when it checks an `rfl` about it, and a proof built from the
lemma `Nat.modLt` unfolds that lemma's induction:

| `rfl` proof **[run]** | Time |
|---|---|
| `Nat.modLt 1001 1000 = Nat.modLt 1001 1000` | 3.1 s |
| same at 10,000 | over 60 s (stopped) |
| `(wrap 10000 10001).value = 1`, proof field from `Nat.modLt` | over 60 s (stopped) |
| `(wrap 1000000 1000001).value = 1`, same | `E-RESOURCE` (recursion limit) after 5.5 s |
| `wrap 1000000 1000001 = wrap 1000000 1`, **proof field by decision** (below) | 0.14 s, whole file |
| Run-time test at 1,000,000 with the `Nat.modLt` proof | passes (proofs are erased when running) |

The fix is to build the range proof by *deciding* it, not by citing the
lemma:

```
def Mod.ofNat [n: Nat] (x: Nat): Mod n :=
  if h: Nat.leq (Succ (x % Succ (n - 1))) (Succ (n - 1)) = True then { value = x % Succ (n - 1), isLt = h }
  else Void.absurd (h (Nat.modLt x (Succ (n - 1))))
```

For closed numbers the native `Nat.leq` gives `True`, so the proof is just
`rfl`; the lemma is only used in the branch that never runs. The general
fact `(Mod.ofNat x).value = x % Mod.size n` is then a three-line lemma by
`match` on the decision, which checks **[run]**. Today's `Dial.fromInt` builds
its proof with `Int.modNatLt`, so it presumably has the same trap
[inferred, not run]; the proof-irrelevance proposal
([proof-irrelevance.md](proof-irrelevance.md), D1′) skips proofs when
*comparing*, which may or may not stop this *evaluation* [unverified].

### 5.2 `Mod 0`

Every `Mod n` must have a zero for the `Add` instance. Three choices:

| | `Mod 0` is | Precedent | Cost |
|---|---|---|---|
| a | **one value, 0**: the modulus is `Mod.size n = Succ (n - 1)`, which is `n` except that it's 1 for 0 | mathcomp's `'Z_p`, "integers mod `max p 2`" | none; laws hold for every `n` with no case split |
| b | `Nat`, unreduced (Mathlib's `ZMod 0 = ℤ`) | Mathlib | every law and `neg` split on `n = 0`; `Mod.neg` on `Nat` has no inverse, so it breaks down |
| c | a type error: instances ask for `n != 0` | Lean's `NeZero` | the instance-rule change of §4 |

(a) is what the prototype does, and nobody wants arithmetic mod 0. (c) is the
cleaner meaning, and could replace (a) later without changing any program
that uses `Mod n` with `n > 0`.

### 5.3 Laws

With (a), the modulus `Succ (n - 1)` is visibly non-zero, so the library's
`%` lemmas apply with no `auto` argument. The prototype's `Add` instance
**[run]**:

```
theorem Mod.assoc [n: Nat] (i: Mod n) (j: Mod n) (k: Mod n): Mod.add (Mod.add i j) k = Mod.add i (Mod.add j k) :=
  Mod.ext (Mod.add (Mod.add i j) k) (Mod.add i (Mod.add j k))
    (Eq.trans (Nat.modAddMod (i.value + j.value) k.value (Succ (n - 1)))
      (Eq.trans (Eq.cong (t => t % Succ (n - 1)) (Nat.addAssoc i.value j.value k.value))
        (Eq.sym (Nat.addModMod i.value (j.value + k.value) (Succ (n - 1))))))
```

`Mod.ext` (same `value`, same `Mod`) is proved like `Char.ext`, with
`Bool.uniqueEq` for the two proofs [checked: `std/core.sw`]. `zeroAdd` and
`comm` are one line each. `Mul` needs `Nat.mulModMod`-style lemmas first
(§1). `Mod 1` has `one = 0`, which is fine: all its laws are `0 = 0`.

### 5.4 Literals

D165 stands: no generic literals. `Mod.ofNat 50` (wrapping) and `Mod.ofInt`
(Euclidean, through the existing `Int.modNat`) make values, and the type comes
from context: `def dial: Mod 100 := Mod.ofNat 50`. `Mod.ofNat 150: Mod 100` is
50, as Lean's `(150 : Fin 100)` is. `Fin.ofNat` keeps its `auto` range proof,
so an out-of-range position is still a compile-time error. If generic
literals ever come, a `Mod` literal out of range should be an error (Idris),
not wrap (Lean): a literal `150` meaning 50 is a typo more often than not.

### 5.5 Subtraction and negation

Without a `Sub` interface `-` stays `Nat`/`Int`, so `Mod` has
`Mod.neg i = Mod.ofNat (size - i.value)` and `Mod.sub i j = i + Mod.neg j`
(wrapping: `5 - 7` is 98 in `Mod 100`; `Nat`'s `5 - 7` is 0). Written
`a.sub b`. A lawful subtraction interface (a group: `neg` with
`x + neg x = zero`) would fit `Int` and `Mod` but not `Nat`, whose `-`
truncates, so `-` would mean two different things by type. Not worth it for
one type.

### 5.6 Equality, order, show, JS

A record whose fields are data and proofs of equations in `Bool` gets `==`
and `<` derived, proof fields left out ("`Dial` by its `position`")
[checked: docs/syntax.md, Interfaces]. `Show` should print the number, as
`Fin`'s does. In JS a `Mod n` is `{ value: 50n }` [checked: docs/core.md,
records are plain objects with proof fields erased]; whether it can cross the
export boundary as a parameter is [unverified].

### 5.7 Conversions

`Mod.ofNat`, `Mod.ofInt`, `.value` (as `Nat`), `Mod.toInt`;
`Fin.toMod: Fin n -> Mod n` (always fine) and
`Mod.toFin [auto ok: n != 0]: Mod n -> Fin n` (needs `size = n`, true for
`n != 0`).

## 6. Recommendation

**Keep `Fin n` as it is, the type of positions, with no arithmetic; add
`Mod n`, numbers modulo `n`, whose `+` and `*` wrap.** The wall in §4 means
Lean's `(50 : Fin 100) + x` can't be had on any `Fin` without changing the
instance rules, the literal rules and the operator table, and the one
language that has it is moving wrap-around away from its index type because
of silent bugs. A separate `Mod n` needs no language change, costs one
library file, keeps `Vec` and day 4 untouched, and gives day 1 the
`+`-without-`% 100` that Lean users liked. The prototype for its `Add`
instance checks today **[run]**.

### 6.1 API sketch

```
-- std/Mod/Mod.sw
-- `Mod n`: the numbers 0 to n - 1, where adding and multiplying wrap
-- around, as on a clock. For positions in a `Vec`, use `Fin n`.
-- `Mod 0` has one value, 0, so that every `Mod n` has a zero.
type Mod (n: Nat) = { value: Nat, isLt: value < Mod.size n }

def Mod.size (n: Nat): Nat := Succ (n - 1)

def Mod.ofNat [n: Nat] (x: Nat): Mod n          -- x % n, proof by decision (§5.1)
def Mod.ofInt [n: Nat] (x: Int): Mod n          -- Euclidean: ofInt (-1): Mod 100 is 99
def Mod.toInt (i: Mod n): Int
def Mod.neg (i: Mod n): Mod n
def Mod.sub (i: Mod n) (j: Mod n): Mod n        -- i + neg j
def Mod.toFin [auto ok: n != 0] (i: Mod n): Fin n
def Fin.toMod (i: Fin n): Mod n                 -- in Fin.sw or Mod.sw

theorem Mod.ext: (i: Mod n) -> (j: Mod n) -> i.value = j.value -> i = j
theorem Mod.valueOfNat [n: Nat] (x: Nat): (Mod.ofNat x: Mod n).value = x % Mod.size n
theorem Mod.valueAdd, Mod.valueMul, Mod.valueSub   -- .value of each operation

instance Mod.instAdd [n: Nat]: Add (Mod n)      -- zero = ofNat 0
instance Mod.instMul [n: Nat]: Mul (Mod n)      -- one = ofNat 1
instance Mod.instShow [n: Nat]: Show (Mod n)    -- "50"
-- `==`, `<`: derived (proof field left out)
```

### 6.2 Day 1 part 1 under the recommendation

This runs and passes the puzzle's example **[run]** (prototype file, with the
`Mod` definitions above it):

```
-- How far a turn moves the dial, as a number modulo 100.
def Turn.offset: Turn -> Mod 100
  | Left n  => Mod.ofInt (-n.toInt)
  | Right n => Mod.ofNat n

def solvePart1 (turns: List Turn): Nat :=
  turns
    |> .scanLeft (pos t => pos + t.offset) (Mod.ofNat 50)
    |> .drop 1
    |> .count (pos => pos == Mod.ofNat 0)
```

Lean's, for comparison (tenthmascot):
`l.scanl (· + Fin.intCast ·) (50 : Fin 100) |>.count 0`. The differences are
`Mod.ofNat 50` for `50`, and `Mod.ofInt` in place of the cast. Today's
`Dial.move` does the same with `Dial.fromInt highest (d.position.toInt ±
n.toInt)`. Part 2 still counts whole turns with `/`, as it does in every
language (§3.2 of the community comparison), so `Mod` doesn't shorten it.

### 6.3 Migration

None for existing code: `Fin`, `Vec`, day 4 and the examples are unchanged.
Day 1's `Dial highest` could become `Mod (Succ highest)` (45 references, most
in the part 2 proofs, which reason about `Int.modNat`); worth doing only if the
proofs don't grow, so as its own ticket after `Mod` exists (D318).

### 6.4 Effort

One lane (Sonnet): `std/Mod/Mod.sw` about 150-200 lines (definitions,
`ext`, value lemmas, the two instances with laws); three `Nat` lemmas for
`*` modulo `d` in `std/Nat/Arith.sw` (about 40 lines); tests beside the code;
an `examples/accept/mod.sw`; a paragraph in docs/syntax.md (Interfaces) and
the library index. About half a day.

### 6.5 Risks

- **Two "numbers below n" types.** Someone reaches for `Fin` and finds no
  `+`. Mitigation: the doc comments point at each other, and the error for
  `+` on `Fin` ("there's no `Add` instance for `Fin 3`") could gain a note
  "for numbers that wrap, use `Mod n`".
- **`Mod 0` has one value** — surprising if met, but nobody wants mod 0.
- **The proof-evaluation trap** (§5.1) bites anyone who builds a `Mod` value
  with a lemma-built proof and then proves things about it by `rfl`. The
  library's constructors avoid it; `Mod.ext` is the way to compare by hand.
- **`a.sub b` instead of `a - b`** reads less like Lean.

## 7. Decisions

| ID | Question | Options | Recommendation |
|---|---|---|---|
| D311 | Wrapping arithmetic: on `Fin` itself, or a separate type? | (1) instances on today's `Fin`; (2) rebuild `Fin` as a record with wrapping `+ - *`; (3) keep `Fin` for indices, add a separate modular type; (4) explicit `+%`/`Fin.addWrap` | [3] |
| D312 | Name of the new type | `Mod n`; `ZMod n` (Mathlib); `Modular n` | [`Mod n`] |
| D313 | What is `Mod 0`? | (a) one value, 0 (modulus `Succ (n - 1)`, as mathcomp's `max p 2`); (b) unreduced `Nat`, as Mathlib's `ZMod 0 = ℤ`; (c) a type error, by allowing `[auto ok: n != 0]` in instance contexts | [(a) now; (c) only if a second use wants instance premises] |
| D314 | Representation | record `{ value, isLt }` with the range proof built by decision; or by `Nat.modLt` | [record, proof by decision (§5.1, measured)] |
| D315 | `-` on `Mod` | named `Mod.sub`/`Mod.neg`; or a new `Sub` interface for `-` | [named functions; no `Sub` interface for now] |
| D316 | Literals | `Mod.ofNat` / `Mod.ofInt`, which wrap; D165 (no generic literals) stands. If generic literals come later, out-of-range `Mod` literals are errors, not wrapped | [yes] |
| D317 | `Fin` itself | unchanged (inductive, no arithmetic), plus `Fin.toMod`/`Mod.toFin`; or switch to a record now | [unchanged, plus the conversions] |
| D318 | Day 1's `Dial` | rewrite as `Mod (Succ highest)` now; later, as its own ticket, only if the proofs don't grow; never | [later, own ticket] |

## Appendix A: other languages

| Language / library | Bounded-index type | Wrapping `+` on it? | Where wrapping lives | Literals out of range | Source |
|---|---|---|---|---|---|
| Lean 4 core | `Fin n`: `{ val, isLt }` | yes, `+ - *` all `% n` | on `Fin`; `UInt*` and `BitVec` (built on `Fin`) | wrap, given `[NeZero n]` | [Fin/Basic.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Data/Fin/Basic.lean), [reference](https://lean-lang.org/doc/reference/latest/Basic-Types/Finite-Natural-Numbers/), [Zulip 2022](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/Fin.20without.20wrapping.html) |
| Lean `Array`/`Vector` indexing | `Nat` + proof (`GetElem`) | n/a | n/a | proof by tactic | [GetElem.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/GetElem.lean) |
| Mathlib | `Fin n` | `+` from core; ring and `Nat` cast opt-in (`open Fin.CommRing`) | `ZMod n` (`ZMod 0 = ℤ`, else `Fin`) | n/a | [PR #25476](https://github.com/leanprover-community/mathlib4/pull/25476), [ZMod/Defs.lean](https://raw.githubusercontent.com/leanprover-community/mathlib4/master/Mathlib/Data/ZMod/Defs.lean) |
| Agda stdlib | `Fin n`, inductive | no: `_+_` widens to `Fin (toℕ i + n)`; `_-_` needs a proof; `pred zero = zero` | `_mod_ : ℕ → (d) → {NonZero d} → Fin d` | `fromℕ<` needs a proof | [Data/Fin/Base.agda](https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Data/Fin/Base.agda), [DivMod.agda](https://raw.githubusercontent.com/agda/agda-stdlib/master/src/Data/Nat/DivMod.agda) |
| Idris 2 base | `Fin n`, inductive | yes, `Num (Fin (S n))`, `Neg`; `finS` wraps | on `Fin`; also `restrict` | compile-time proof required | [Data/Fin.idr](https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Data/Fin.idr), [Arith.idr](https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Data/Fin/Arith.idr) |
| mathcomp | `'I_n`: `nat` + proof | named functions `Zp_add`, `Zp_mul`, `Zp_opp`; cyclic `ordS` | ring on `'Z_p` = mod `max p 2` | n/a | [fintype.v](https://raw.githubusercontent.com/math-comp/math-comp/master/boot/fintype.v), [zmodp.v](https://raw.githubusercontent.com/math-comp/math-comp/master/algebra/zmodp.v) |
| Rocq stdlib | `Fin.t`, inductive | [unverified] | `Z/nZ` libraries [unverified] | — | — |
| Haskell `finite-typelits` | `Finite n` | yes, `Num` wraps | on `Finite`; also widening `add`, `multiply` | run-time error | [Integral.hs](https://raw.githubusercontent.com/mniip/finite-typelits/master/src/Data/Finite/Internal/Integral.hs), [Data.Finite](https://hackage.haskell.org/package/finite-typelits/docs/Data-Finite.html) |
| Haskell `modular-arithmetic` | — | — | separate `Mod i n` | `toMod` wraps | [Data.Modular](https://hackage.haskell.org/package/modular-arithmetic/docs/Data-Modular.html) |
| Rust | `usize` | `+` checked in debug, wraps in release | `wrapping_add`, `Wrapping<T>` | — | [RFC 560](https://raw.githubusercontent.com/rust-lang/rfcs/master/text/0560-integer-overflow.md) |
| Zig | integers | no: overflow is illegal | `+%` (wrap), `+|` (saturate) | — | [Zig docs](https://ziglang.org/documentation/master/) |
| Go | unsigned ints | yes, by the spec | the default | — | [Go spec](https://go.dev/ref/spec#Arithmetic_operators) |
| Java | `int` | wraps [unverified from the JLS] | `Math.addExact` throws; `Math.floorMod` | — | [Math](https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/lang/Math.html) |
| C | `unsigned` | wraps; signed overflow is undefined [unverified from the standard] | — | — | — |
| Dafny | `newtype` with bounds | no: a result out of range is a proof obligation | `bv8` etc. wrap | — | [Dafny reference §5.7, §5.2.3](https://dafny.org/latest/DafnyRef/DafnyRef) |
| F* | `UInt32.t` | no: `add` requires no overflow | `add_mod`; `add_underspec` | — | [FStar.UInt32.fsti](https://raw.githubusercontent.com/FStarLang/FStar/master/ulib/FStar.UInt32.fsti) |

Not found: a Zulip thread proposing to remove core Lean's `Add (Fin n)`, or a
user report of being bitten by `Fin` subtraction wrapping; the strongest
statements are Mathlib's PR and Reid Barton's comment. A 2012 Agda post found
the standard `Fin` awkward for roll-over counters and wrote its own
([erdi.dev](https://erdi.dev/blog/2012-02-19-mod-n_counters_in_agda/)).

## Appendix B: measurements

All **[run]** with `target/release/stitchwort check` (or `test`) on scratch
files, one at a time, while other lanes were running; times are wall clock,
including about 0.1-0.4 s of start-up and library loading.

| Program | Result |
|---|---|
| `Fin.toNat (Fin.ofNat 9999: Fin 10000) = 9999 := rfl` (and 999) | 0.10 s |
| `Fin.toNat (Fin.ofNat 999999: Fin 1000000) = 999999 := rfl` | 1.29 s, 1.1 GB peak memory |
| `def x: Fin 100 := 50` | `E-TYPE-MISMATCH`: "a numeral can only be the prelude's `Nat` or `Int`" |
| `instance [m: Nat]: Add (Below (Succ m))` | `E-INSTANCE-HEAD` |
| `instance [n: Nat] [auto ok: n != 0]: Add (Below n)` | `E-INSTANCE-CONTEXT` |
| `Mod n` prototype: `ext`, `ofNat`, `ofInt`, `add`, `neg`, `sub`, `DecEq`, `Add` instance with `zeroAdd`, `assoc`, `comm`; day 1 part 1 on the example; `Mod.ofNat 50 + Mod.ofNat 60 = Mod.ofNat 10` by `rfl` in `Mod 100`; `Mod 0` | checks; 5 tests pass |
| `Nat.modLt 1001 1000 = Nat.modLt 1001 1000 := rfl` | 3.1 s |
| same at 10,000 | stopped at 60 s |
| `.value = 1 := rfl` on a `Mod`/record value with a `Nat.modLt` proof: modulus 1,000 / 10,000 / 100,000 / 1,000,000 | 1.9 s / over 60 s / over 60 s / `E-RESOURCE` at 5.5 s |
| the same values at 1,000,000 in a run-time `test` | passes |
| record with the proof built by decision: `wrap 1000000 1000001 = wrap 1000000 1 := rfl`, and the general `(wrap n x).value = x % n` by `match` on the decision | 0.14 s, checks |
