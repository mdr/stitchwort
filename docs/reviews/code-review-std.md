# Code review: the standard library in Stitchwort (`crates/elab/src/std/`)

SW-1987, 7 Nov 2026. Read only; nothing built or run. Scope: the 96 `.sw`
files under `crates/elab/src/std/` (33.8k lines), plus the Rust code that binds
natives and run bodies to them, where that decides what a std edit may change
silently. The Rust-only crate reviews of today (`code-review-*.md`) and the
1 Nov whole-codebase review covered no `.sw` code, so there are no earlier
findings in scope to give a status for.

## Summary

The library is in good shape for its age. Definitions are total and mostly
structural; the fuel-driven loops (`Parse.many`, `findAll`, `recursive`,
`Nat.divFuel`, `Nat.digitsOnto`) are given provably enough fuel and fail rather
than truncate; the integer divisions check out case by case; `Map` and `Set`
are a weight-balanced tree with O(1) `size`; the sort is a stable bottom-up
merge sort. The house style is clean: no `And`/`Or`/`Not`/`Iff` in a
statement, no parenthesised ability rows, no `Cons` patterns. Every public
`def` has a doc comment except a dozen instances. The problems are at the
level of the API as a whole. Only `List` and `NonEmptyList` take effectful
callbacks. The same operation has different names and argument shapes on
different types. Requested lemmas sit in files named for something else, and
the friction notes show several were written again because nobody found them.
`omega` reads `Nat.max` but `List.maximum` produces `Ord.max`. A handful of std
definitions are replaced or rewritten by the backends by name only. Most of
those are already in SW-1885's pin table, but `List.length`'s run body is
missing from it.

**Top five recommendations**

1. Give `Array`, `Map`, `Set` and `Option` the `{e}` callbacks `List` has, for
   `map`, `foldLeft`, `foldRight`, `filter`, `filterMap`, `any`, `all`,
   `count` and `find` (S1, D2821).
2. Bridge `Ord.max`/`Ord.min` at `Nat` to `Nat.max`/`Nat.min` with lemmas, so
   `List.maximum`, `NonEmptyList.maximum` and `maxBy` results reach `omega`
   (S2).
3. Move the lemmas the notes couldn't find to the files named for them, and
   add the ones two or more days wrote themselves (S4, S3).
4. Add `List.length`'s run body to SW-1885's pin table and guard it (S5).
5. Settle one name per operation across the collections, and fix the stale
   and wrong API docs (S7, S9, D2822).

**Counts:** 0 high, 5 medium, 8 low.

## Findings

| # | Where | What | Severity | Confidence | Size |
|---|---|---|---|---|---|
| S1 | `Array/Array.sw:108-128`, `Map/Map.sw:78-298`, `Set/Set.sw:45-98,185-193`, `Option/Option.sw:6-96` | Only `List` and `NonEmptyList` take effectful callbacks; `Array`, `Map`, `Set`, `Option` and `Text` callbacks must be pure | medium | high | M |
| S2 | `List/Toolkit.sw:96-103,640-668`, `NonEmptyList/NonEmptyList.sw:91-110`, `Nat/Arith.sw:500-503`, `elab/src/omega.rs:149-150` | `List.maximum`/`minimum`/`maxBy` give `Ord.max`/`Ord.min` terms; `omega` knows only `Nat.max`/`Nat.min`, and no lemma links them | medium | high | S |
| S3 | (across std) | Functions and lemmas that two or more AoC days wrote themselves are still missing | medium | high | M |
| S4 | `List/SortLemmas.sw:26,1009,1328`, `Parse/Reads.sw:486`, `Mod/Mod.sw` | Lemmas live in files named for something else; the notes record five cases where an existing std item was missed | medium | medium | M |
| S5 | `elab/src/lib.rs:3035-3069`, `core/Data.sw:81-93`, `docs/proposals/backend-trust.md` §3.1 | `List.length`'s run body is swapped in by name, isn't hashed, and isn't in the pin table; nothing in std marks the name-bound definitions | medium | high | S |
| S6 | `List/Toolkit.sw:298-306`, `core/Helpers.sw:8`, `List/Toolkit.sw:787` | Two definitions for one operation: `List.elem`/`List.contains` (`elem` unused), `List.concatMap`/`List.flatMap` (separate lemmas, no bridge) | low | high | S |
| S7 | (across std) | One operation, several names or shapes: `getOrElse`/`getOr`, `minimum`/`min`, `split`/`splitOn` against `join`/`joinWith`, `Text.fold` a right fold, `Set.intersect`, `List.inRange`, `List.rangeFrom`'s order | low | high | M |
| S8 | `Array/Array.sw`, `Set/Set.sw`, `Text/*.sw`, `core/Result.sw`, `Parse/Parse.sw:227` | Gaps in operation families: `Array` lacks `filter`/`find`/`foldRight`/`reverse`/`contains`/`take`/`drop`/`append`, and `Array.sum` is `Nat`-only; no `Set.find`, `Text.reverse`/`map`/`filter`/`trimStart`/`trimEnd`/`replace`, `Result.getOr`/`isErr`, `Char.isAsciiDigit` | low | high | M |
| S9 | `core/Data.sw:19-20`, `List/Toolkit.sw:7-15,72,258-260,576-582,741,752`, `Text/*.sw` | API docs that are stale or wrong: `Nat.add`'s computation, parameter names that don't exist, the list of effectful callbacks, which `Text` ops run natively | low | high | S |
| S10 | `Map/Map.sw:220,290-302`, `Set/Set.sw:39,87-93,190-193`, `Nat/Bits.sw:56-62` | Needless O(n) work: `Map.range` filters the whole map, `Map.find`/`any`/`all`/`count` build `toList` first, `Set.any`/`all`/`isSubset`/`disjoint` never stop early, `Set.fromList` skips `Map.fromList`'s sorted fast path; the bit operations recurse per bit with no native | low | medium | M |
| S11 | (across std) | 1,543 of 2,960 theorems have no doc comment; whether D2351 covers theorems is unsettled | low | high | (D2820) |
| S12 | e.g. `List/Toolkit.sw:48,340,554`, `Text/Basics.sw:129,192` | Loop and step helpers (`List.filterStep`, `mapAccumLeftGo`, `partitionStep`, `Text.splitCons`, `wordsStep`, …) are public API, in completion and search | low | high | L (D2823) |
| S13 | `Nat/Iterate.sw:8,41`, `List/Toolkit.sw:300`, `core/Result.sw:45` | Argument order differs between similar operations: `Nat.iterate count step seed` against `iterateUntilStable x step …`, and a decision procedure first in `List.decEq` but last in `List.elem` | low | medium | S |

## Details

### S1. Effectful callbacks only on `List` (medium, high)

The `List` toolkit's header (`List/Toolkit.sw:7-21`) promises that `map`,
`filter`, the folds, `count`, `any`, `all`, `find`, `filterMap`, `findMap`,
`takeWhile`, `flatMap`, `partition` and `span` take a callback `a → {e} b`, with
the pure case compiling to the same loop. `NonEmptyList` follows suit. Nothing
else does. `Array.map`, `Array.foldLeft` (`Array/Array.sw:108-128`), every
`Map` and `Set` traversal, `Option.map`/`flatMap`/`any`/`all`, and `Text.any`/
`all`/`count` take pure callbacks.

Scenario: a day keeps its records in a `Map` and checks each with
`Fail.ensure` while folding. It must write `m.toList.foldLeft …`. That allocates
the entry list and loses the map's own lemmas (`Map.foldLeftToList` has to be
applied by hand). The same goes for an `Array` of rows parsed with `Fail`, and
for `option.map Range.read`.

Recommendation: give these the same `{e}` rows, defined through the `List`
versions where they already go through `toList`, and through the tree folds
for `Map`/`Set`. The doc's "with a pure callback the row is empty" argument
carries over, so existing lemmas keep their statements. M, Sonnet, after D2821.

### S2. `omega` can't read `List.maximum` on `Nat` (medium, high)

`List.maximum`/`minimum` fold with `Ord.max`/`Ord.min`
(`List/Toolkit.sw:96-103`), and so do `maxBy`, `minBy`, `maximumOf` and the
`NonEmptyList` versions. `Ord.max` is `match Ord.compare x y` (`Ord/Ord.sw:41`),
and `Nat.compare` is `if Nat.equal … else if Nat.leq …` (`core/Ordering.sw:16`).
`Nat.max`/`Nat.min` are separate definitions, `if Nat.leq m n` (`Nat/Arith.sw:500-503`).
`omega` treats only `Std.Nat.max` and `Std.Nat.min` as atoms (`omega.rs:149-150`),
and grep finds no lemma equating the two forms. A proof about
`(rows.map length).maximum` therefore meets an `Ord.max` that `omega` can't use,
while `List.maxLength` (`List/Grid.sw:69`) uses `Nat.max`. The same quantity
has two normal forms.

Recommendation: add `Ord.maxNat (m n: Nat): Ord.max m n = Nat.max m n` and
`Ord.minNat`. Their `NonEmptyList` and `List.maximumSome` corollaries can then
be stated with `Nat.max`. Optionally, `omega` could also unfold `Ord.max` at
`Nat.instOrd` (a separate Opus change). S, Sonnet for the lemmas.

### S3. Missing functions and lemmas that days wrote themselves (medium, high)

These come from the friction notes (`aoc/NOTES-2020.md`, `-2021.md`,
`-2024.md`, `docs/research/aoc-2020-friction-days-10-20.md`) and `aoc/src/Aoc/`.
I checked each against std with grep. Open tickets are named where they
exist.

- **`Nat.lcm`, coprimality, Euclid's lemma, a congruence solver.** There is no
  `lcm` anywhere in std. Evidence: NOTES-2020:3530, the friction note's line 296.
  This is SW-1493, in the backlog.
- **Count by a proposition linked to `List.count`.** `List.NumberWith`
  (`List/SortLemmas.sw:1009`) has only `numberWithUnique` and `numberWithCong`.
  Three days hit it (NOTES-2020:5391, 5503; friction note 55, 255-262). This is
  SW-1577.
- **`List.countFilterMap`.** Written twice, in two forms:
  `Year2020/Day11/Proofs/Sight.sw:17` and `Year2024/Day14/Proofs/Lemmas.sw:19`.
- **`takeWhile` step lemmas** (`p x = True → [x, ..xs].takeWhile p = [x, ..xs.takeWhile p]`,
  and the `False` case): `Year2020/Day10/Proofs/Part2.sw:33,35`, NOTES-2020:2675.
- **A non-empty collection has a member.** Written for `Set`
  (`Year2020/Day20/Proofs/Monsters.sw:157`) and for `List`
  (`Year2024/Day19/Proofs/Possible.sw:54`). Std has only the converse,
  `Set.sizePositive`.
- **`Set.min` is at most every member** (NOTES-2024:4986, 5198). Std has
  `containsMin`, `minToList` and `popMin*`, but no "least" lemma.
- **`List.lengthFilterMapLe` and `List.mapConcat`** (NOTES-2021:250-253;
  `Common/Proofs/GridCells.sw:97`).
- **`Result.getOr`, `Result.isErr`** (NOTES-2020:3328); only `getOrElse`
  and `isOk` exist.
- **Monotone division, `a ≤ b → a / d ≤ b / d`**, and
  **`a ≠ 0 → b ≠ 0 → a * b ≠ 0`** (NOTES-2021:1684, 1761;
  `Year2024/Day14/Proofs/Lemmas.sw:30`).
- **Generic lemmas sitting in AoC grid files:** `withIndexFromMap`,
  `indexFromAbove` and `pairExt` (`Common/Proofs/GridCells.sw:90,149,109`),
  and `somePairInjective` (`Common/Proofs/BitReader.sw:10`).

Also asked for, but with one day each or a design behind them: a fuelled
"iterate until stable" without a measure (NOTES-2020:3113), a heap and
union-find (NOTES-2021:3671, NOTES-2024:4966, 5670), and the bit lemmas
`testBitSmall`/`testBitAbove` (`Year2024/Day24/Proofs/Lemmas.sw:10,14`).

Recommendation: one Sonnet lane for the list, the `Set` lemmas and `Result`,
which are the ones with two or more users. SW-1493 and SW-1577 stay their own
lanes.

### S4. Lemmas where nobody looks (medium, medium)

- **`List/SortLemmas.sw` holds much more than sorting.** It has
  `List.sumCons` (`:26`), `List.sumAppend` (`:29`), `List.productCons`
  (`:1328`), `List.NumberWith` (`:1009`) and `Nat.leqTotal`; its header admits
  "Gauss, counting occurrences, keys, subsequences … sliding windows".
- **`Text.toNatDigits`, the spec of `Text.toNat`,** is in `Parse/Reads.sw:486`.
  `Text.toNat`'s doc links it, but a search under `Text/` misses it.
- **The `Int.modNat` lemmas are in `Mod/Mod.sw`** (NOTES-2024:4354).
- **The notes record existing items missed**: `Pair.instOrd` (NOTES-2020:5703
  says "std has none for pairs"; it is `core/Ord.sw:124`), `Text.toNatSome`
  (NOTES-2020:885), `List.splitBy` (day 6 wrote `groupsOf` first,
  NOTES-2020:1554), `Nat.pigeonhole` (NOTES-2020:1820), and `List.tailOf`
  (NOTES-2024:373).

Recommendation: move the sum, product and count lemmas to `List/Lemmas.sw`
(or a `List/Sums.sw`), `Text.toNatDigits` to `Text/Text.sw`, and the
`Int.modNat` lemmas to `Int/`. Names don't change, so callers don't either.
Regenerate the hash snapshots and run the `hash_stability` test. Also consider
a `tail` doc alias line on `tailOf` ("Haskell's `tail`"), because people search
for that word. M, Sonnet.

### S5. What the natives and rewrites assume of std, and `List.length`'s run body (medium, high)

Inventory of std definitions whose meaning code outside std assumes:

| Std definition | Bound in | By | A std edit that keeps the binding but changes meaning |
|---|---|---|---|
| `Text`, its 17 text natives (`toList`, `fromList`, `append`, `length`, `isEmpty`, `decEq`, `compare`, `uncons`, `fold`, `trim`, `take`, `drop`, `contains`, `split`, `join`, `Nat.toText`, `Text.toNat`) | `rt/natives.rs:51-136` | content hash, covering dependencies (`Char.isWhitespace` for `trim`) | none: any edit unbinds (silently slow) |
| `Int`, `Nat`, `SafeNat`, `SafeInt` representations and the `Int` natives | `rt/natives.rs:199-340` | content hash | none (silently slow) |
| `Array` and its 8 natives (`size`, `get`, `getOr`, `getLt`, `set`, `push`, `pop`, `replicate`) | `rt/natives.rs:782-905` | content hash, all or nothing | none: a stale one refuses the program |
| `Float` and its kernel natives | `core/float.rs` | content hash | none: refuses the library |
| `Nat.add`'s second-argument rules (`Nat.addZero`, `Nat.addSucc`) | `core/nat_add.rs` | content hash plus the theorems' types | none (silently off) |
| Kernel Nat natives: `Nat.add`, `sub`, `mul`, `leq`, `equal`, `divFuel`, `decEq`, `equalRefl`, `equalSound`, `equalFalse` | `core/native.rs:395-491` | type shape only | **any body edit that keeps the type**, for example making `Nat.sub` saturate differently (SW-1885, F2) |
| Effect natives: `Effect.bind`, `foldComp`, `translate`, `runPure` | `rt/effect.rs`, `js/effect.rs` | name, arity, `Comp`'s shape | any body edit that keeps the shape (SW-1885, D2710) |
| Rewrites: `Bool.ifThenElse`, `Decidable.toBool` (fused with the `decEq` natives), `Decidable.elim`, `Effect.handlePlus`, `runPure`, `CompIn`; in JS also `Ord.compare`, `Ord.fromCompare`, `List.append`, `Nat.add` | `rt/lower.rs:369,748-770`, `rt/fusion.rs:118-139,464`, `js/lib.rs:2349-2354` | name | for example `Decidable.toBool` returning the opposite, or `Bool.ifThenElse` reordering its branches: the backends keep the old meaning (listed in backend-trust.md §3.1) |
| **`List.length` runs as `List.lengthOnto xs 0`** | `elab/src/lib.rs:3035,3048-3069` | name (`Builtin::ListLength`, `ListLengthOnto`) | **an edit to `List.lengthOnto`, or to `List.length`, that `List.lengthOntoEq` no longer states**. The run body is type-checked but "never unfolded by the kernel, and not hashed (it's determined by the body)" (`core/globals.rs:106-113`). That holds for the `decreasing` and lifted-`match` run bodies, but this one isn't determined by `List.length`'s body at all. |

`List.length`'s run body is the only row not in backend-trust.md's table or in
SW-1885's plan. Today `List.lengthOntoEq` would fail to check if
`lengthOnto` changed meaning, so the risk is an edit that changes or removes
both together. The runtimes would then count differently from the definition
the proofs use. Nothing in `core/Data.sw` says that the backends bind or
rewrite any of the core definitions above, apart from the doc lines on `Nat` and
`List.lengthOnto`.

Recommendation: (a) in SW-1885's `pins.rs` table, pin `List.length` and
`List.lengthOnto` by content hash, or at least require `List.lengthOntoEq` with
its exact statement before setting the run body, as `nat_add` requires
`Nat.addZero` and `Nat.addSucc`. (b) Above each name-bound core definition,
add one `--` line: "The backends bind this by name (`crates/core/src/pins.rs`):
change it together with the pin". That is the warning an editor of std needs,
and the comment rules allow it, because the code can't say it. S, Opus (it
belongs with SW-1885).

### S6. Two definitions for one operation (low, high)

- **`List.elem`** (`List/Toolkit.sw:298-302`) takes its decision procedure as
  an argument. Nothing in std, `aoc/` or `games/` calls it. `List.contains` is
  the one with lemmas (`List.memContains`). Delete `elem`.
- **`List.concatMap`** (`core/Helpers.sw:8`, pure, recursive) and
  **`List.flatMap`** (`List/Toolkit.sw:787`, `{e}`, `concat ∘ map`) are the same
  function with different definitions. `concatMap` has only `memConcatMap`;
  `flatMap` has `memFlatMap`, `lengthFlatMap` and `flatMapCong`. Nothing
  equates them, and 2025 day 1's proofs and `Rogue/Render.sw:38` use
  `concatMap`. Add `List.concatMapFlatMap: List.concatMap xs f = List.flatMap xs f`,
  and say in `concatMap`'s doc that user code should use `flatMap`. The core
  still needs `concatMap` before `List.map` exists.
- **`List.count` and `List.occurrences`.** These are deliberate: one is a
  loop, the other the shape proofs want, and `List.countOccurrences` links
  them. They are listed here only as checked.

S, Sonnet (fold into the S9 lane).

### S7. One operation, several names (low, high)

- **The fallback getter.** `Option.getOrElse` and `Result.getOrElse`, against
  `List.getOr`, `List.headOr`, `Array.getOr`, `Map.getOr` and
  `NonEmptyList.getOr`. All take a value, not a thunk.
- **The smallest element.** `List.minimum` and `NonEmptyList.minimum`, against
  `Set.min` and `Map.min`. All are the smallest element of a collection.
  (`Ord.min` and `Nat.min` are binary, which is why the list one is `minimum`.)
- **`Text` splitting and joining.** `Text.split` and `Text.join` take a
  `Char`; `Text.splitOn` and `Text.joinWith` take a `Text`. The inverse of
  `splitOn` isn't called `joinOn`, and `List.joinWith` pipes while
  `Text.joinWith` is `@[noReceiver]`.
- **`Text.fold` is a right fold** (`Text/Basics.sw:26`), with no `foldLeft`.
  Every other collection has `foldLeft` and `foldRight`.
- **Set algebra.** `Set.intersect` sits beside `union` and `difference`. `Map`
  has `intersectWith` but no key-only `intersect`.
- **Predicate names.** `Set.disjoint` sits beside `Set.isSubset`.
- **Misplaced or misordered helpers.** `List.inRange (x) (from) (until)`
  (`List/Toolkit.sw:544`) is a `Nat` predicate in `List`'s namespace, so
  `x.inRange 0 5` doesn't find it. `List.rangeFrom (count) (start)` reads as
  "range from count".
- **Repetition.** `Text.repeat text count`, against
  `List.replicate count x` and `Array.replicate count x`.
- **Three "space" tests with different sets.** `Parse.isSpace` is space or tab,
  `Char.isAsciiSpace` is the six ASCII whitespace characters, and
  `Char.isWhitespace` is Unicode's `White_Space`. Each doc is right, but
  `Parse.isSpace` is the one a newcomer guesses wrong.

`length` against `size` (`List`, `Text` and `NonEmptyList` against `Array`,
`Map` and `Set`) is common practice in other languages, so I'd leave it.

Recommendation: D2822. Judged by the end state alone (migration cost doesn't
count), rename to `Option.getOr` and `Result.getOr`, `Text.fold` to
`Text.foldRight` with a new `Text.foldLeft`, `Text.joinWith` to `Text.joinOn`,
`Set.intersect` to `Set.intersection` (or `Map.intersectWith` to
`Map.intersectionWith`), `Set.disjoint` to `Set.isDisjoint`, `List.inRange` to
`Nat.inRange`, and `Parse.isSpace` to `Parse.isSpaceOrTab`. Leave
`minimum`/`min` as it is. M, DeepSeek (mechanical sweep across std, aoc,
games, docs and the guide, with hash snapshots).

### S8. Gaps in operation families (low, high)

- **`Array`** has `map`, `mapWithIndex`, `foldLeft`, `any`, `all`, `count`,
  `withIndex` and `sum`. It has no `filter`, `find`, `findIndex`, `foldRight`,
  `contains`, `reverse`, `append`, `take`, `drop` or `zip`. `Array.sum`
  (`Array/Array.sw:133`) is `Array Nat → Nat`, while `List.sum` takes any
  `Add`.
- **`Set`** has no `find`. `Map` has one, and `Set.min` is no substitute for a
  search with a predicate.
- **`Text`** has no `reverse`, `map`, `filter`, `indexOf`, `replace`,
  `trimStart`, `trimEnd`, `takeWhile`/`dropWhile` or `toUpper`/`toLower`
  (ASCII). Days go through `toList` for each of these.
- **`Char`** has `isAsciiLetter`, `isAsciiLowercase`, `isAsciiUppercase` and
  `isAsciiAlphanumeric`, but no `isAsciiDigit`. That one lives as
  `Parse.isDigit` (`Parse/Parse.sw:227`).
- **`Result`** has no `getOr` (see S7) and no `isErr`.

These are user-visible std functions, so the lane updates `docs/guide/` too.
M, Sonnet.

### S9. API docs that are stale or wrong (low, high)

- **`Nat.add`** (`core/Data.sw:19-20`): "It recurses on its first argument, so
  `Succ m + n` computes to `Succ (m + n)`". Since SW-787 (`core/nat_add.rs`),
  `x + 0` and `x + Succ n` compute as well, so `c + 1` is `Succ c`. The doc
  should say so. NOTES-2024:824 ("`c + 1` doesn't compute") shows users
  believing the old rule.
- **Docs that name parameters the function doesn't have.**
  - `List.rangeFrom` (`List/Toolkit.sw:258-260`): "`n` numbers counting up from
    `i`", where the parameters are `count` and `start`.
  - `List.findIndexFrom` (`:741`) and `List.withIndexFrom` (`:752`):
    "counting from `i`", where the parameter is `start`.
  - `List.chunksOfPositive` (`:576-582`) says "`n` elements" and describes the
    `n = 0` case. The parameter is `size`, and `size ≠ 0` is required, so that
    case can't happen.
- **The toolkit header** (`List/Toolkit.sw:7-15`) lists the functions with
  effectful callbacks, but misses `forEach` and `mapWithIndex`.
- **`List.scanLeft`** (`:72`) says "Haskell's `scanLeft`"; Haskell's is
  `scanl`.
- **`Text`'s natives aren't in its docs.** `Array`'s header says which
  operations are O(1) when run. `Text`'s docs never say that `trim`, `split`,
  `contains`, `length` and the rest are natives at run time, so a reader of
  `Text.length = text.toList.length` assumes O(n) list work.

S, Sonnet, with S6.

### S10. Needless O(n) work (low, medium)

- **`Map.range`** (`Map/Map.sw:301`) filters the whole map. It could split the
  tree in O(log n + k).
- **`Map.find`, `any`, `all` and `count`** (`:220,290-298`) build `m.toList`
  before scanning, and `Set.toList` maps over `Map.toList`.
- **`Set.any` and `Set.all`** (`Set/Set.sw:87,190`) are folds with `acc ∨ p key`
  and `acc ∧ p key`, so they visit every key after the answer is known.
  `isSubset` and `disjoint` inherit this. Changing them means re-proving
  `Set.foldAll` and its neighbours.
- **`Set.fromList`** (`:39`) folds `insert`. `Map.fromList` has an O(n) path
  for sorted input (`Map.Raw.fromListFast`) that `Set.fromList` could reach
  through `Map.fromList (xs.map (k => (k, ())))`.
- **`Nat.xor`, `and`, `or` and `shiftLeft`** (`Nat/Bits.sw`) take one
  well-founded step per bit, each a few divisions. NOTES-2024:7118 found them
  the slowest part of a day. There are no runtime natives for them, although
  there are for `+`, `-`, `*`, `/` and `<=`.

The notes' Map timings (about 2 µs a lookup, 7 µs an insert) are runtime costs,
not std definitions, and belong to the `rt` reviews.

Recommendation: the `Set.fromList` and `Map.range` changes are a Sonnet lane;
bit natives would be an extension of the `INT_NATIVES` pattern (Opus, with
SW-1885's pins).

### S11. Theorem docs (low, high)

1,543 of 2,960 `theorem`s have no `--|` doc. Most are named for what they say
(`Map.getInsert`, `Set.containsRemoveOther`). A doc on those would restate the
name, which the comment rules forbid. D2351 asks for "full API docs" for std
without saying whether that means theorems. D2820.

### S12. Internal helpers are public API (low, high)

Helpers that exist for the checker's sake are visible to completion, `search`
and dot lookup on a list or text. Some have `@[noReceiver]` and others don't.
Examples: `List.filterStep`, `partitionStep` and `partitionOnto`,
`mapAccumLeftGo`, `findMapStep` and `maxByStep`; `Text.splitCons`,
`wordsStep`, `wordsClose` and `splitOnLoop`; `Nat.divStep`. Their docs are
honest about being steps, but nothing stops `xs.filterStep`. The language has
no `private`, so this is a design question (D2823), not a cleanup.

### S13. Argument order (low, medium)

- `Nat.iterate (count) (step) (seed)` puts the start last, while
  `Nat.iterateUntilStable (x) (step) (measure) (shrinks)` puts it first.
- `List.decEq`, `Result.decEq` and `NonEmptyList.decEq` take the decision
  procedure first; `List.elem` takes it last (S6 deletes `elem`).
- `Map.Raw`'s operations take the key first (`Map.Raw.insert key value m`), but
  `Map.Raw.getOr m key d` takes the map first. `Map.Raw` is internal, but it is
  public (S12).

## Checked and sound

- **Integer division.** `Int.div`/`mod` (Euclidean), `tdiv`/`tmod` and
  `fdiv`/`fmod` (`core/Int.sw:132-152`, `Int/Basics.sw:39-77`): every
  constructor case checked by hand on ±7 / ±2 and -18 / 100, including the exact
  multiples. Division by 0 follows the total-division change (`x / 0 = 0`,
  `x % 0 = x`) in every definition and doc. `Int.modNat`'s 0 case matches its
  doc.
- **Fuel.** `Nat.divFuel`, `Nat.digitsOnto`, `Parse.manyFuel`, `findAllFuel`
  and `recursiveFuel` are given enough fuel by a stated argument (characters
  left + 1, or `n + 1`), and a round that reads nothing stops the parse with an
  error instead of returning a truncated result. D2543 holds.
- **Sorting.** `List.sortWith`'s bottom-up merge sort is stable: `pushRun` and
  `mergeRuns` always merge the older run on the left. It is O(n log n), and the
  docs say so.
- **`Map` and `Set`.** O(1) `size` and `isEmpty` (stored sizes); O(log n)
  `get`, `insert`, `remove`, `min`, `max`, `below` and `above`; `insertWith`'s
  `f new old` convention is the same in `Map.insertWith`, `fromListWith`, the
  raw tree and their docs; `union` keeps the first map's value as documented.
- **The kernel Nat natives' doc.** The list on `Nat` (`core/Data.sw:9-14`) is
  exactly `Native::ALL` (`core/native.rs:73-83`).
- **Hash-pinned natives cover their dependencies.** `def_hash` closes over
  dependencies, so editing `Char.isWhitespace` unbinds `Text.trim`'s native
  rather than desyncing it.
- **House style.** Across all 96 files: no `And`/`Or`/`Not`/`Iff` written as a
  proposition (only the accessors `And.left` and `Iff.forward`), no
  parenthesised ability rows, and no `Cons x xs` patterns; `Cons` is used only
  as a function.
- **Doc coverage of `def`s.** Every public `def` and `type` has a `--|`
  comment, except the `decLessEq`/`decLessThan` instances on `Int` and `Float`,
  a few `instance`s in `core/DecEq.sw`, `Show.sw` and `Ord.sw`, and the
  `Parse.RunsExamples` fixtures.
- **Doc examples spot-checked against definitions.** `Text.splitOn` (the
  "aaa"/"aa" case), `Text.split ""`, `Text.toInt` ("-0", "+5", "-"),
  `Text.lines` (CR handling), `List.windows` (`size = 0`), `List.chunksOf`,
  `List.maxBy`'s tie rule and its Haskell contrast, `Map.groupBy`,
  `Map.indexBy` and `Map.mapKeys` ("the later key's value wins").
- **Superseded friction.** `List.length` no longer runs out of stack: it runs
  as `lengthOnto`. `+` computes on its second argument. `Option.someBeqSome`
  and `List.beqCons` cover the `==` friction.

## Tickets to file

- **Lane A, std docs and duplicates (Sonnet, 45 min).** The S9 doc fixes;
  delete `List.elem` and add `List.concatMapFlatMap` (S6); add
  `Ord.maxNat`/`Ord.minNat` and their `List.maximum`/`NonEmptyList` corollaries
  (S2). Run `snap:hashes` and the `hash_stability` test.
- **Lane B, effectful callbacks beyond `List` (Sonnet, 60-90 min, after
  D2821).** S1, for `Array`, `Map`, `Set` and `Option`. Update the guide's
  effects page.
- **Lane C, lemmas days wrote themselves (Sonnet, 60 min).** From S3:
  `countFilterMap`, the `takeWhile` step lemmas, "non-empty has a member" for
  `List` and `Set`, `Set.minLeast`, `lengthFilterMapLe`, `mapConcat`,
  `Nat.divMonoLeft` and `Nat.mulNeZero`. Move the `GridCells` and `BitReader`
  generic lemmas into std, and have the days drop their copies. SW-1493 and
  SW-1577 stay separate.
- **Lane D, lemma relocation (Sonnet, 45 min).** S4: sums, products and
  `NumberWith` out of `SortLemmas.sw`; `Text.toNatDigits` to `Text/`; the
  `Int.modNat` lemmas to `Int/`. Run `snap:hashes`.
- **Lane E, family gaps (Sonnet, 60 min).** S8: the `Array` operations and a
  generic `Array.sum`, `Set.find`, the `Text` functions, `Char.isAsciiDigit`,
  `Result.isErr`, with guide updates.
- **Lane F, naming sweep (DeepSeek, 60 min, after D2822).** S7, as decided,
  across std, aoc, games, docs and the guide.
- **Fold into SW-1885 (Opus).** S5: pin `List.length` and `List.lengthOnto`, or
  require `List.lengthOntoEq`, and add the `--` note to each name-bound core
  definition.
- **Lane G, `Set.fromList` fast path and `Map.range` by split (Sonnet, 45
  min).** From S10. Bit natives are a separate Opus ticket beside SW-1885.
- **After D2823, an Opus design note on internal helpers (S12).**

## Questions for Matt

- **D2820:** Does D2351's "full API docs" cover theorems? 1,543 of 2,960 have
  none, and most are named for what they state. [rec: no. Document a theorem
  only when its statement doesn't say it all: a why, which direction to use,
  or the form `rewrite` wants. No sweep.]
- **D2821:** Extend `{e}` callbacks from `List`/`NonEmptyList` to `Array`,
  `Map`, `Set` and `Option` (`map`, `foldLeft`, `foldRight`, `filter`,
  `filterMap`, `any`, `all`, `count`, `find`)? [rec: yes, as lane B]
- **D2822:** Rename for one name per operation (S7): `Option`/`Result.getOr`;
  `Text.fold` → `Text.foldRight` plus a new `Text.foldLeft`; `Text.joinWith` →
  `Text.joinOn`; `Set.intersect` → `Set.intersection`; `Set.disjoint` →
  `Set.isDisjoint`; `List.inRange` → `Nat.inRange`; `Parse.isSpace` →
  `Parse.isSpaceOrTab`; no aliases kept? [rec: yes]
- **D2823:** Internal helpers (`List.filterStep`, `mapAccumLeftGo`,
  `Text.wordsStep`, …) are public API. Should an Opus design note propose a
  way to hide them (an `@[internal]` attribute or a naming rule that search and
  completion honour)? [rec: yes, after the current kernel work]
