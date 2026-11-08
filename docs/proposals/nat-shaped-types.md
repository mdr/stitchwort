# Proposal: types shaped like `Nat` run as machine numbers

**Status:** Draft 1, 8 November 2026 (SW-2397, from D3423). Design only:
nothing was built or run for it except a read-only scan of the sources. The
questions for Matt are in [§9](#9-open-questions).

**Stage 1 as built** (SW-2398, after SW-2415 and SW-2405): `Data::nat_shape`
takes which fields a backend stores, and the fast runtime passes
`erasure::stored_fields`, so `Fin` qualifies once SW-2415 stopped storing
its determined index (while `STITCHWORT_CHECK_REBUILDS` is on, cells keep
that field and `Fin` stays cells). Steps and frames are unchanged (the
example's limits, 562 steps and 11 frames, are the same either way, since
SW-2405 makes `Succ (f x)` a loop as TRMC did for the cell). Native
instructions, same build with and without the rule: 2025 day 3 1.487 G →
1.428 G (-4.0%), 2021 day 9 1.736 G → 1.660 G (-4.3%), 2021 day 15 -0.2%,
2021 day 11 and 2025 days 4 and 7 within ±0.1%. The rest of the gain
waits for stage 2's natives (`Fin.toNat` still walks).

**Stage 2 as built** (SW-2399): `Fin.toNat` and `Fin.ofNatLt` are bound by
content hash in `stitchwort_rt::natives` (`FIN_NATIVES`, beside the other
runtime-only natives, until SW-1991 moves those pins into core), and only
while `Fin` is Nat-shaped, so not under `STITCHWORT_CHECK_REBUILDS`. Rather
than a new primitive, a bound definition is lowered as a function returning
its number parameter, which the simplifier inlines at every direct call: no
new code in the machine, the codec or native code, and no steps at an
inlined call (one frame as a closure). The example's least step limit goes
from 562 to 263 (frames 11 either way). Native instructions, same build
with the binding switched off and on, median of 3: 2025 day 3 1.428 G →
1.342 G (-6.0%), 2021 day 9 1.661 G → 1.593 G (-4.1%), 2021 days 11 and 15
-0.1%, 2025 days 4 and 7 unchanged; answers identical.

Claims about Stitchwort were checked at commit `36dfba35d`. Labels:

- **[checked: S]**: read in S (a file in this repository, or a URL);
- **[scan]**: a read-only script over the `.sw` sources (§2.2);
- **[measured: S]**: a number measured earlier, by S;
- **[inferred]**: my reasoning from checked facts;
- **[estimated]**: a number reasoned out, not measured;
- **[from memory]**: believed, not confirmed against a source here.

## 0. Summary

- **The problem.** std's `Fin n` is a unary data type, `FZero | FSucc (i:
  Fin n)`, and it runs that way: the number 9 is nine heap cells, and
  `Fin.toNat` walks them. `Nat` itself is unary only for the kernel; at run
  time it is a machine number. So `Fin` is the slow way to hold a number that
  is already known to be small. Every comparison of two digits in 2025 day 3
  walks both digits; a `Fin`-indexed array would walk up to n cells per
  read, which is why the dense-distances index takes a `Nat` instead
  (D3419). The kernel's view of `Fin` is fine as it is.
- **The change.** At run time, represent every data type whose constructors,
  after erasing indices and proofs, are "one with no fields and one with one
  field of the same type" as a machine number, exactly as `Nat` is: the
  first constructor is 0, the other is +1, and matching is "is it 0, else
  take one off". One function in `stitchwort_core` decides it, beside
  the one that unboxes one-field records (D866), so the interpreter, native
  code and JavaScript agree. Then bind `Fin.toNat` and `Fin.ofNatLt` to
  runtime natives that return their number unchanged, pinned by content
  hash as std core's natives are. The kernel, the checker's evaluator and
  every proof stay as they are.
- **What it should do.** A `FSucc` goes from a heap cell (about 23 ns to
  build, check and free, measured for tree nodes, `cell-allocator.md`) to an
  add on a machine word (about 1 ns) **[estimated]**; `Fin.toNat` and
  `Fin.ofNatLt` go from O(number) frames to O(1). On today's AoC programs
  the gain is modest: 2025 day 3's search, whose comparisons are `toNat`
  walks, maybe 1.5-3x faster; 2021 days 9, 11 and 15 about unchanged (their
  digits are converted once, at parse time; day 15's `Fin` work is under
  0.1% of its 48 G instructions) **[estimated]**. The real gain is that
  `Fin` stops being a type to avoid in code that runs: a `Fin`-indexed
  array read becomes one bounds check instead of a walk of up to 260,000
  cells on day 15's scale.
- **Work.** About 3.5-5 lane-hours in three stages, the JS one optional
  ([§8](#8-estimate-and-plan)).

## 1. What Stitchwort has today

### 1.1 `Fin` and its users

`Fin` is an indexed family [checked: `crates/elab/src/std/Fin/Fin.sw:7`]:

```stitchwort
type Fin: Nat → Type =
  | FZero: Fin (Succ n)
  | FSucc (i: Fin n): Fin (Succ n)
```

**Correction (SW-2406):** the next sentence is wrong. D141 stores the
implicit `n` at run time (`FSucc(4, FSucc(3, FZero(2)))`, and `Fin.toNat`
reads it to pass its own implicit argument), so `FSucc` has two run-time
fields and `Fin` isn't Nat-shaped until those fields are dropped:
[erase-determined-fields.md](erase-determined-fields.md). The same
correction applies to §2.2's "`Fin` … yes" and §2.3's "Extra erased fields"
and "A field of the same family at another index".

The implicit `n` in each constructor is an erased field; `FSucc`'s `i` is
its only runtime field. `Fin.toNat` is structural recursion
(`FSucc i => Succ (Fin.toNat i)`), `Fin.ofNatLt n i lt` builds `i` `FSucc`s.
`Fin`, `FZero`, `FSucc` and `Fin.ofNatLt` are library built-ins in the
registry, for `Fin` literals [checked: `crates/core/src/registry.rs:346-352`;
`fin-literals.md`]: `(3: Fin 10)` elaborates to `Fin.ofNatLt 10 3 rfl`.

Only two std files match on `FZero`/`FSucc` (Fin.sw, 32 uses; Vec.sw, 20)
[scan]. The rest of std and `aoc/` reach `Fin` through `toNat`,
`ofNatLt`, `ofNatCheck`, its `DecEq`/`Ord` instances (both via `toNat`) and
`Char.toDigit`/`Parse.digit`, which give a `Fin 10` [checked: Fin.sw;
`std/Parse/Parse.sw:262`]. The `aoc/` users [checked: grep]:

| Day | Use | Hot? |
|---|---|---|
| 2021 day 9 | `HeightMap = { grid: Grid (Fin 10) }`; `heightAt` maps `Fin.toNat` on every lookup | per lookup, ≤ 10 frames |
| 2021 day 11 | digits mapped to `Nat` once (`Cavern.ofDigits`) | parse only |
| 2021 day 15 | `Cave = { grid: Grid (Fin 10) }`, `levels` maps `toNat` once | parse only |
| 2025 day 3 | `Battery = Fin 10`; `pick` compares with `candidate < x` (`Ord.byKey Fin.toNat`) | inner loop: two walks per comparison |
| 2025 day 7 | `start: Fin width`, `rows: List (Vec Bool width)` | a few reads |
| `Aoc.Common.Grid` | imports `Fin` | — |

### 1.2 How `Nat` is a machine number now

The kernel keeps `Nat` inductive, with compact literals and natives
(`native-numbers.md`). The fast runtime decides representation in lowering
[checked: `crates/rt/src/lower.rs`, `natives.rs:603`]:

- `Representation::nat` is the prelude's `Nat`, only if its content hash is
  `NAT_DATA_HASH` [checked: `natives.rs:274-282`]; the runtime refuses to
  lower without it (`lower.rs:349`).
- **Construction** (`lower.rs:1022-1040`): `Succ`s around `Zero` are a
  literal; `Succ (Succ x)` is `Prim(Nat Add, [x, 2])`.
- **Matching** (`lower.rs:1212`): `MatchKind::Nat`, compiled to `NatCase`
  (is it 0?) and `NatPred` (take one off) [checked: `code.rs:854-864`].
  The optimiser folds a match on a known literal [checked: `opt.rs:1065`].
  `NumSwitch` is for the kernel's literal-match terms, so only for `Nat`
  [checked: `ir.rs:240`; `lower.rs` `num_case`].
- **Values** are `Value::Nat(u64)`, or `Value::BigNat` past a word
  [checked: `value.rs:34-37`]; the add prim moves to big numbers by itself.
- **JS** compiles `Nat` to `bigint`: `x === 0n` and `x - 1n` for a match
  [checked: `crates/js/src/lib.rs:3067-3071`], decided separately by
  `self.nat` at about ten sites.
- Native code compiles the same `Image` as the interpreter (`crates/native`
  has no representation decisions of its own) [checked: grep `nat_data`].

`Int`, `Text` and `Float` get the same treatment, each tied to its pinned
declaration.

### 1.3 The structural precedent: one-field records (D866)

A record with exactly one runtime field is that field at run time, decided
by `Data::unboxed_field` [checked: `crates/core/src/globals.rs:546-566`]:
"Only how a value is stored changes: nothing about the type, its checking
or its hash", and every backend "decides by this one function, so they
agree on the layout". It is automatic, by shape, with no attribute. This
proposal is the same kind of rule for a second shape.

It already gives Lean's `Fin` for free: std's `Mod n` is
`{ value: Nat, isLt: value < Mod.size n }` [checked: `std/Mod/Mod.sw:14`],
and `SafeNat` is `{ value: Nat, fits: … }` [checked: `std/Int/Safe.sw:17`];
both are machine numbers at run time today.

### 1.4 What a `Fin` costs today

- `FSucc i`: a `Value::Data(1, Fields)` cell, one allocation [checked:
  `value.rs:48`; `lower.rs` generic ctor path]. `FZero` is `Value::Tag(0)`,
  no allocation.
- A match on a `Fin`: a generic constructor switch, a field load and a
  reference count.
- `Fin.toNat i`: i + 1 frames, not a tail call; `Fin.ofNatLt n i _`: i
  frames and i cells.
- `Fin.all n`, `Fin.any n p`: O(n²) whatever the representation (see §10,
  finding 1).

## 2. Which types

### 2.1 The rule

A data type `D` (any parameters, any indices) is **Nat-shaped** when:

1. it is data, not a proposition (`Sort::Prop` types are erased whole);
2. it has exactly two constructors;
3. after erasure (the constructor's `field_erased`: indices, implicits,
   proofs, ghost fields), one constructor has no runtime fields (the zero)
   and the other has exactly one (the successor);
4. that field's type is `D` itself, applied to anything (other indices,
   other parameters), after unfolding definitions to its head;
5. it is not a record (a record has one constructor, so 2 already excludes
   it) and not one of the hash-pinned native types (`Nat`, `Int`, `Text`,
   `Float`), which keep their own paths.

Its run-time form is a `Nat` value: the zero is 0 and the successor of `x`
is `x + 1`. The decision is one function in `stitchwort_core::globals`,
`Data::nat_shape() -> Option<NatShape { zero: u32, succ: u32, field: usize
}>`, beside `unboxed_field`, and every backend calls it.

Laziness, which Idris 2 excludes (`Lazy Natural`), doesn't arise:
Stitchwort fields are strict.

### 2.2 What qualifies

From a scan of every two-constructor type with a field of its own type in
`crates/elab/src/std`, `aoc/src`, `games/` and `examples/` [scan], plus
reading the candidates:

| Type | Where | Nat-shaped? |
|---|---|---|
| `Nat` | std core | yes, but kept on its pinned path (rule 5) |
| `Fin` | std `Fin.sw` | **yes**: the only new one in std |
| `Fin` | `examples/accept/indexed-families.sw`, `examples/reject/implicit-field-dependent.sw` | yes (test copies) |
| `List` (`Empty | More (rest: List)`) | `examples/accept/namespaces.sw` | yes (a Peano type under another name) |
| `Ty` (`TNat | TList (t: Ty b)`) | `examples/accept/indexed-families.sw`, `examples/soundness/large-index.sw` | yes: a family in `Type 1` whose field has another index |
| `Le`, `Even`, `Sums` | examples | no: propositions, erased whole |
| `Fnat` (`FZero | FSucc (n m: Fnat) (same: n = m)`) | `examples/soundness/nested-recursive-field.sw` | no: two runtime fields |
| `Tree`, `Num`, `Number`, `Vec` | examples, 2021 day 18 | no: a constructor with two runtime fields |

Nothing in `aoc/` or `games/` declares a Nat-shaped type of its own. So
in practice the rule means `Fin`, and whatever users write later.

### 2.3 Edge cases

(Correction, SW-2406: a constructor's implicit index field, `FSucc`'s `n`,
is stored at run time under D141, not erased; see §1.1's note and
[erase-determined-fields.md](erase-determined-fields.md).)

- **Parameters.** Not stored in values, so they don't matter: a
  `type Count (a: Type) = | None | One (rest: Count a)` qualifies.
- **Extra erased fields.** Ignored, by rule 3: `FSucc [n: Nat] (i: Fin n)`
  is one runtime field. A proof field, or a ghost field
  (`erase-proof-data.md`), is the same.
- **Constructor order.** The zero is whichever constructor has no runtime
  fields, not the first. `| Succ (x: T) | Zero` qualifies, and lowering maps
  constructor indices to `MatchKind::Nat`'s arm order (zero first) through
  `NatShape`. Agda's `BUILTIN NATURAL` and Idris 2's check both accept
  either order (§6).
- **Mutual types.** `Even`/`Odd`-like pairs, whose successor field is the
  other type, don't qualify under rule 4. They could be numbered too (a
  pair of mutually Nat-shaped types is two views of one number), but
  nothing uses them; leave them out.
- **A field of the same family at another index** (`Fin n` inside `Fin
  (Succ n)`, `Ty b` inside `Ty (List b)`): qualifies; the index is erased.
- **A field through a definition** (`type T = | Z | S (x: Alias)` with
  `Alias := T`): rule 4 unfolds to the head, as `Fin`'s field type is
  already in normal form.
- **`Int`-like shapes** (two constructors, each with one runtime field of
  type `Nat`, or of a Nat-shaped type): a second rule could make them
  signed numbers, `A n` as `n` and `B n` as `-n - 1`. The only such type is
  `Int`, already native [scan]. Not proposed (§9, Q4).
- **Deep patterns** (`FSucc (FSucc i)`): the elaborator compiles nested
  patterns to nested one-level matches, so this is two `NatCase`/`NatPred`
  pairs, as for `Succ (Succ k)` on `Nat` today [inferred]. A later
  optimisation could test `x >= 2` once, for both types; not needed for
  this.
- **Impossible arms** (`Fin 0` has no values): stay `Expr::Unreachable`
  [checked: `lower.rs:1235-1238`].
- **Literals.** A numeral is never a `Fin` in the kernel; `(3: Fin 10)` is
  `Fin.ofNatLt 10 3 rfl`. With the stage 2 native, lowering gives
  `Prim(…, [10, 3])`, and constant folding makes it the literal 3
  [inferred].

## 3. What changes at run time

| Part | Today | Proposed |
|---|---|---|
| `FZero` | `Tag(0)` | literal `0` |
| `FSucc i` | a cell `Data(1, [i])` | `Prim(Nat Add, [i, 1])`; a chain of k `FSucc`s around `FZero` is the literal k, as for `Succ` (`lower.rs:1022`) |
| `match i` | `MatchKind::Data` switch | `MatchKind::Nat` (`NatCase`, `NatPred`), arms reordered by `NatShape` |
| `NumSwitch` | `Nat` only | unchanged: it comes from the kernel's literal matches, which `Fin` doesn't have |
| `Fin.toNat` | i + 1 frames | stage 1: still i + 1 frames, but no cells; stage 2: a native, the identity |
| `Fin.ofNatLt n i _` | i frames, i cells | stage 1: i frames, no cells; stage 2: a native returning `i` |
| `Fin.ofNatCheck`, `Char.toDigit`, `Parse.digit`, `Fin.toMod`, `Mod.toFin`, `DecEq`, `Ord` | via `toNat`/`ofNatLt` | O(1) once those are natives, with no natives of their own |
| arithmetic | none on `Fin` | none: `Fin` has no `+` (fin-arithmetic.md); `Mod n` is the wrapping type |
| printing, `Show` | `Nat.toText (Fin.toNat i)` | the same code, O(1) |
| big numbers | n/a | as for `Nat`: `u64`, then `BigNat` by the add prim |
| interpreter, native code | — | both run the lowered `Image`, so both get it from the lowering change; native code already compiles `NatCase`/`NatPred` |
| JS (stage 3) | a tagged object per `FSucc` | `bigint`, through the same `nat_shape` call at the `self.nat` sites |

**The runtime natives** (stage 2) follow the pattern of the `Int` and
`Float` runtime natives: a table of (native, content hash) bound by
`bind_natives` [checked: `natives.rs:578-590`], to move into
`stitchwort_core::pins` with `assumed_by` naming the runtime (SW-1991). The
hash of `Fin.toNat` covers `Fin` itself (`pins.rs:12`), so a bound native
implies the declaration whose shape it was written for. Binding also
asserts `nat_shape(Fin)` is `Some`, so a native can never see a `Fin` that
isn't a number. `Fin.ofNatLt`'s native ignores `n` and the proof and
returns `i`; the bound is the proof's job, as with every erased proof.

**The JS boundary.** Indexed families can't cross it ("is an indexed
family, which can't cross the JS boundary yet") [checked:
`crates/js/src/lib.rs:414-416`], so `Fin`'s interface is unaffected. A
non-indexed Nat-shaped type (`namespaces.sw`'s `List`) can cross today as
a tagged object; stage 3 keeps that boundary form, converting in its codec,
so no `.d.ts` changes (§9, Q3).

### 3.1 The boundary with the kernel

The kernel never sees a runtime value, so its view doesn't change:

- **Lowering is one-way.** It reads checked terms and emits IR; nothing
  turns a runtime value back into a term [checked: `stitchwort_rt` is used
  by the driver's `run.rs`, `test_run.rs` and `counterexample.rs` only;
  `crates/core/src/native.rs` names it in a doc comment; grep found no value
  printer in `rt`, `driver`, `cli` or `lsp`].
- **What comes back** from the runtime: a test's `Bool` tag, `IO`'s text and
  numbers, a counterexample search's pairs and `Bool`s (warnings only, not
  trusted), and JS exports (families excluded). None is a `Fin`.
- **Conversion, `decide`, `rfl` and `Finite.check`** run on the checker's
  own evaluator over terms (`crates/core/src/value.rs`, `machine.rs`),
  where `Fin` stays `FZero`/`FSucc` and `Fin.ofNatLt n k rfl` unfolds one
  `FSucc` at a time when something looks inside (fin-literals.md). The
  kernel spec (`docs/core.md`) doesn't change, and neither does any proof.
- **The reference runner** (the driver's, on the checker's evaluator) keeps
  unary `Fin`; it and the fast runtime agree on outputs, which is what
  their tests compare (`tick_counts.rs`).

## 4. Step counts and agreement

**Steps on the fast runtime are frames entered**; constructing, matching
and number prims cost none, except the extra words of a big number
[checked: `machine.rs:22-24`; `prims.rs:429-447`; inferred that a small
prim is free]. So:

- **Stage 1 changes no step counts.** `FSucc` and matches were free and
  stay free; `Fin.toNat` still enters i + 1 frames.
- **Stage 2 lowers them** wherever `Fin.toNat`, `Fin.ofNatLt` or something
  built on them runs: `Fin.toNat i` goes from i + 1 steps to none. Counts
  only fall, so a program within its step limit today stays within it. This
  is what `Nat`'s natives already do to `Nat.add` and the rest.
- **Ticks** (the partial-program counter `tick_counts.rs` compares across
  runners) count `Tick` operations, which this doesn't touch [checked:
  `crates/rt/tests/it/tick_counts.rs:1-13`].
- **The checker's budget** is the kernel evaluator's and doesn't change.
- **Counterexample search** gets more inputs into its per-input step budget
  (`FAST_STEPS`) when they involve `Fin`; it gets cheaper, never different.

**Recommendation:** accept the lower counts, as for `Nat`'s natives, with
no "virtual steps" to keep the old ones (§9, Q2).

**Agreement tests** (stage 1, then 3):

- An `examples/accept` program with a Nat-shaped type in each constructor
  order, a parameter, an erased proof field and an index, matching deep and
  shallow, with `test`s, run on the interpreter, native code and `run --js`.
  The outputs are the agreement check: the representation is invisible, so
  any difference is a bug.
- `crates/rt` lowering tests that `FSucc (FSucc FZero)` lowers to a
  literal and a `Fin` match to `MatchKind::Nat`, and that `Fnat` (two
  runtime fields) and a mutual pair don't.
- `validate.rs` already checks a `MatchKind::Nat` has arms with 0 and 1
  fields [checked: `validate.rs:166`]; that keeps covering reordered arms.
- Stage 2: the natives' own differential test, as for the `Int` natives:
  each native against its definition on the kernel's evaluator for every
  `i < n` up to a few hundred.

## 5. Trust and soundness

The kernel is untouched, and no proof depends on the runtime (§3.1), so
nothing here can make a false theorem check. What can go wrong is a wrong
answer at run time, and each case has a guard:

1. **A type detected wrongly** (an erased field counted, or a runtime one
   missed): construction and matching would disagree. Guard: one function
   decides for every backend (as `unboxed_field` does), using the same
   `field_erased` that lowering already uses for every other match; the
   validator's arm check; the agreement tests.
2. **Constructor order.** A swapped type with arms not reordered would take
   the wrong branch. Guard: `NatShape` carries the mapping; a test declares
   the successor first.
3. **A pin that isn't the identity.** If `Fin.toNat` were changed to compute
   something else, a bound identity native would be wrong. Guard: the
   content-hash pin, which goes stale with `E-BUILTIN` when the definition
   or `Fin` changes (`pins.rs`); and the native binds only when
   `nat_shape(Fin)` holds.
4. **`ofNatLt` without a bound check.** The native trusts `lt: i < n`, which
   the checker proved; as for every erased proof, the runtime doesn't
   recheck it.
5. **Big numbers.** A `Fin n` value is below n, but n is a `Nat` and can be
   anything; the value uses `Value::Nat`/`BigNat` and the add prim's
   overflow path, exactly as `Nat` does. JS `bigint` has no limit.
6. **Code that inspects runtime values by shape.** The runtime takes apart
   only constructors it fixes (`Shapes`: `Bool`, pairs, lists, `Option`)
   and its own natives' types [checked: `ir.rs:88`; `prims.rs` uses of
   `Value::Data`]; none is Nat-shaped. Stage 1 audits `specialise.rs`
   (`driver_of`), `census.rs` and the allocation trace, which name types.
7. **Caches.** The IR codec is keyed by the runtime's build hash
   [checked: `wire.rs:19-21`], so cached programs lowered the old way are
   never read by the new runtime.

The new trusted pieces are small: `nat_shape` (layout only, like
`unboxed_field`) and two identity natives behind pins.

## 6. Other implementations

| System | Which types | How chosen | Conditions | `toNat`-like conversions | Checked or trusted | Source |
|---|---|---|---|---|---|---|
| **Idris 2** | any Nat-shaped type, including indexed ones | **automatic** (`calcNaty`), plus `%builtin Natural T` to insist (an error if the shape is wrong) | 2 constructors; after erasure one with 0 arguments, one with exactly 1, whose type has the same type constructor; strict, not `Lazy` | detected by pattern: `cast Z = 0`, `cast (S k) = 1 + cast k` becomes the identity, "sensitive to seemingly insignificant changes"; or asserted by `%builtin NaturalToInteger` / `IntegerToNatural` | shape checked; `IntegerToNatural` and `%transform` rewrites are trusted ("It is your responsibility") | builtins.rst; `TTImp/ProcessData.idr` `calcNaty`; `Compiler/Opts/Constructor.idr` ("Nat hack"); `Compiler/Opts/Identity.idr`; `TTImp/ProcessBuiltin.idr` |
| **Idris 1** | Nat-like families | **flag**, `--optimise-nat-like-types` (1.3.2) | "after erasure, two constructors, one nullary, the other one with exactly one recursive field" | [from memory: `Nat` ops hard-coded] | compiler's | Idris-dev CHANGELOG, "New in 1.3.2" |
| **Agda** | the one type bound by `BUILTIN NATURAL` | **declared** | shape `zero`/`suc`, either order | bound functions (`NATPLUS`, `NATEQUALS`, …) run as primitives on closed terms; `Fin` stays unary | kernel and backends trust the primitives | Agda manual, "Built-ins: Natural numbers" |
| **Lean 4** | `Nat`, `Int` special; any **trivial wrapper** | `Nat` by the kernel and compiler; wrappers automatic | a wrapper: one constructor with exactly one run-time relevant field (and visible enough in a public module) | `Fin` is `structure Fin n where val : Nat; isLt : val < n`, "represented identically to the underlying natural number": `val` is a projection | kernel trusts GMP for `Nat.add` etc.; `@[extern]`, `@[implemented_by]` trusted | Lean reference: Inductive Types, Run-Time Representation; Finite Natural Numbers; Natural Numbers |
| **Rocq extraction** | any inductive the user names | **declared**: `Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))"` | none checked | user-written ML | "not checked at all"; overflow is "the user's responsibility" | Rocq manual, Program extraction, "Realizing inductive types" |
| **F\*** | n/a | by definition | `nat` is `i: int{i >= 0}`; `fin n` is `k: int{0 <= k /\ k < n}`: refinements of `int`, so already machine numbers | coercions are free | the refinement proof | `ulib/Prims.fst:477`; `ulib/FStar.Fin.fsti:40` |
| **GHC** | none Peano-shaped; `newtype` erased | — | — | — | — | [from memory] |
| **Stitchwort today** | `Nat`, `Int`, `Text`, `Float` by pinned declaration; one-field records automatic (D866) | pins; `unboxed_field` | — | `Mod n`, `SafeNat` are records over `Nat`, so already numbers | kernel natives pinned by hash | §1.2, §1.3 |

Notes:

- **Idris 2's base `Fin`.** The docs give `Fin` as an example of an indexed
  type that "can be optimised", but `Data.Fin`'s
  `%builtin NaturalToInteger Data.Fin.finToInteger` is commented out
  [checked: `libs/base/Data/Fin.idr:86`], and its doc comment still says
  `Fin` will be "exceedingly inefficient at run time" (line 15). Detection
  counts arguments not of quantity 0 (`hasArgs`, `ProcessData.idr:249`),
  and `FZ : Fin (S k)` binds `k` implicitly; whether that `k` is at
  quantity 0 (so `Fin` is detected) I didn't confirm **[unverified]**. The
  docs' own `%transform "plus"` example rewrites `plus j k` to
  `j + j`, which shows what unchecked rewrites cost.
- **The theory** is Brady, McBride and McKinna, "Inductive families need not
  store their indices" (TYPES 2003): once indices are erased, `Fin` is
  `Nat` **[from memory]**. Stitchwort already erases the indices; this is
  the next step.

### 6.1 Which approach fits Stitchwort

- **A. Automatic by shape (Idris 2), with hash-pinned conversions
  (Stitchwort's own).** Every Nat-shaped type gets it, users included,
  with nothing to write. Its one rule sits beside D866's and has the same
  justification: layout only, decided in one place. Instead of Idris's
  late pattern detection of identities, or its trusted assertions, the
  conversions are natives pinned by content hash, which Stitchwort already
  trusts for `Nat`, `Int` and `Float` and which go loudly stale. Cost: the
  lowering and JS changes (§8). **Recommended.**
- **B. Declared** (`@[natural]`, as Agda's `BUILTIN` or Rocq's `Extract
  Inductive`). Explicit, but a user who writes a Peano type gets the slow
  version unless they know the attribute; and there is nothing to declare
  that the shape doesn't already say. Idris 2 keeps its pragma only as an
  assertion; Stitchwort could add one later if a user wants an error when a
  type loses the shape.
- **C. Redefine `Fin` as a record over `Nat`** (Lean's `Fin`, F\*'s
  `fin`): `type Fin (n: Nat) = { value: Nat, isLt: value < n }`. It is a
  machine number today with no runtime work (D866). But it changes the
  kernel's `Fin`: `Vec.get` recurses on `FZero`/`FSucc` and would need a
  bound-carrying recursion on `Nat`; Fin.sw's and Vec.sw's 52 pattern uses
  and every proof by matching on `Fin` would be rewritten; and the
  family's index reasoning (an impossible `Fin 0` case refuted by
  coverage) becomes arithmetic on proofs. That is Lean's choice, and
  Stitchwort already has it as `Mod n`. It would also leave every other
  Nat-shaped type unary. Not recommended.
- **D. Fin only** (A's mechanism for one pinned type, as `Nat` is). Less to
  test, but the shape rule is no harder than the pin, and it would need a
  pin on `Fin`'s declaration that the shape rule makes unnecessary.

## 7. What it doesn't do

- No change to the kernel, `docs/core.md`, the checker's evaluator, or any
  statement or proof.
- No `Fin` arithmetic, no literals at `Fin` in the kernel, no `Int`-like
  rule, no mutual pairs.
- No change to D3419 (dense distances' index stays `Nat`-based). Option (a)
  there would become fast enough, but it was also out for its implicit size
  parameter.
- No asymptotic fix for `Vec.get` (it walks the `Vec`, a list, anyway) or
  for `Fin.all` and `Fin.any` (§10).

## 8. Estimate and plan

### 8.1 Speed-ups [estimated]

| Where | Today | After | Basis |
|---|---|---|---|
| one `FSucc` | a cell: about 23 ns to build, check and free | an add on a word, about 1 ns | [measured: cell-allocator.md §1] for tree nodes; ratio estimated |
| `Fin.toNat i`, `Fin.ofNatLt n i _` | i frames (+ i cells for `ofNatLt`) | O(1) (stage 2) | §1.4 |
| 2025 day 3 (`pick`'s `candidate < x`) | two walks of up to 10 cells per comparison | two native compares | 1.5-3x on the solve, not measured |
| 2021 day 9 (`heightAt`) | a walk of ≤ 10 per lookup, beside a grid lookup that walks lists | the lookup alone | small; the lookup dominates |
| 2021 days 11, 15 | parse-time only | — | day 15: about 10 k digits × ~10 frames ≈ 0.1 M frames against 48.4 G instructions [measured: dense-distances.md §1.1]: under 0.1% |
| a `Fin`-indexed array read at cell i (day 15 scale: i up to 260 k) | i frames of `toNat` (~130 k on average) | one bounds check | the difference between unusable and usable |

Stage 1 measures day 3 and a small `Fin` benchmark before and after with
`bench:compare` (as SW-2382 did); the numbers above are replaced by those.

### 8.2 Stages

| Stage | Work | Model | Estimate |
|---|---|---|---|
| 1 | `Data::nat_shape` in core; lowering of constructors, matches (arm order) and `nat_literal` through it; `Representation` and the audit of §5 item 6; validator; lowering tests and the agreement example (interpreter and native); day 3 and a micro-benchmark measured | Opus (representation for every backend at once, where a wrong guess spreads) or Sonnet with an Opus review | 1.5-2 h |
| 2 | Runtime natives for `Fin.toNat` (identity) and `Fin.ofNatLt` (returns `i`), pinned by hash, bound only under `nat_shape`; their differential test; re-measure | Sonnet | 1 h |
| 3 (optional) | JS: the same `nat_shape` at the `self.nat` sites; the boundary form of non-family Nat-shaped types unchanged (codec converts); `run --js` on the agreement example | Sonnet | 1-1.5 h |
| beside | `Fin.all` and `Fin.any` in O(n) (§10) | Sonnet | 0.5 h |

Total about 3.5-5 lane-hours. Docs: the runtime representation is
described where `Nat`'s is (fast-runtime.md is a design record, so the
place is DESIGN.md's runtime section or the `Representation` doc comment);
a sentence in the guide where `Fin` is introduced ("runs as a machine
number"). Not a language feature, so `docs/syntax.md` and the tour don't
change.

## 9. Open questions

- **Q1. Which types.** (a) every Nat-shaped type, automatically (§2.1);
  (b) `Fin` only; (c) types that declare it. **[rec: (a)]**: the same kind
  of rule as D866's one-field records; users' Peano types get it free; no
  pin on `Fin`'s shape needed.
- **Q2. Step counts.** Stage 2's natives make `Fin.toNat` and
  `Fin.ofNatLt` cost no steps instead of i (stage 1 changes none). (a)
  accept that, as for `Nat`'s natives; (b) charge them i steps to keep
  counts. **[rec: (a)]**: counts only fall, ticks and the checker's budget
  don't change, and (b) would keep an O(n) charge for O(1) work.
- **Q3. JavaScript.** (a) stage 3, after stages 1-2 are measured, keeping
  the boundary form of exported Nat-shaped types; (b) now with stage 1;
  (c) not at all. **[rec: (a)]**: `Fin` can't cross the boundary, so no
  interface changes either way; the playground and `run --js` get the same
  speed-up once it's built.
- **Q4. A second rule for `Int`-like shapes.** **[rec: not now]**: the only
  such type is `Int`, already native.
- **Q5. `Fin` in the kernel.** Compact `Fin` values in conversion (as `Nat`
  has literals) would be a kernel change. **[rec: no]**: `Fin.ofNatLt n k
  rfl` is already compact until something looks inside, and no proof has
  been slow because of `Fin`.

## 10. Findings beside this note

1. **`Fin.all n` and `Fin.any n p` are O(n²) at run time.** `Fin.all
   (Succ n)` maps `FSucc` over all of `Fin.all n` at each level, and
   `Fin.any` wraps `p` in one more closure per level, so the k-th test
   goes through k closures [checked: `Fin.sw`, `Fin.all`, `Fin.any`]. The
   representation doesn't change that; an O(n) runtime form (a loop over
   `Nat` with `Fin.ofNatLt`, proved equal, or a pinned native) would. Used
   by `Finite (Fin n)`, so by `Finite.check` over positions.
2. **Idris 2's `%builtin NaturalToInteger` for `Fin` is commented out**
   upstream; worth knowing if anyone compares against Idris's `Fin`
   speed.

## Sources

- Idris 2 manual, "Builtins":
  <https://idris2.readthedocs.io/en/latest/reference/builtins.html>
  (source `docs/source/reference/builtins.rst`).
- Idris 2 sources, `main` branch, read 8 November 2026:
  `src/TTImp/ProcessData.idr` (`calcNaty`, `hasArgs`),
  `src/Compiler/Opts/Constructor.idr`, `src/Compiler/Opts/Identity.idr`,
  `src/TTImp/ProcessBuiltin.idr`, `libs/base/Data/Fin.idr`,
  `CHANGELOG.md` (v0.4.0: "New `%builtin` pragma for compiling user defined
  natural numbers to primitive `Integer`s"):
  <https://github.com/idris-lang/Idris2>.
- Idris 1 CHANGELOG, "New in 1.3.2":
  <https://github.com/idris-lang/Idris-dev/blob/master/CHANGELOG.md>.
- Agda manual, "Built-ins":
  <https://agda.readthedocs.io/en/latest/language/built-ins.html>.
- Lean reference, "Inductive Types" (Run-Time Representation, Trivial
  Wrappers), "Finite Natural Numbers", "Natural Numbers":
  <https://lean-lang.org/doc/reference/latest/>.
- Rocq manual, "Program extraction":
  <https://rocq-prover.org/doc/master/refman/addendum/extraction.html>.
- F\* `ulib/Prims.fst`, `ulib/FStar.Fin.fsti`:
  <https://github.com/FStarLang/FStar>.
