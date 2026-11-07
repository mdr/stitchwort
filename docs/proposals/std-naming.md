# Proposal: one name per operation in std, and how lemmas are named

SW-2179, for SW-2006 (S7 of `docs/reviews/code-review-std.md`, with S6 and
S13) and SW-2177. Draft 1, 7 November 2026. Read only: nothing here was
built or run. Counts are from `grep` over the worktree at `d56c2d00f`; a
count includes qualified uses (`Option.getOrElse`) and dot calls
(`.getOrElse`), and leaves out `docs/proposals/`, `docs/reviews/` and the
AoC `NOTES-*.md` files, which are records and keep the old names.

## 0. Summary

**What a user gets.** One spelling to guess for each operation, whichever
collection it's on: `getOr` on an `Option` as on a `List`, `Map` or
`Array`; `foldLeft` and `foldRight` on `Text` as on everything else;
`intersection` beside `union` and `difference`. Functions live where a dot
call finds them (`x.inRange 0 5` on a `Nat`, `c.isAsciiDigit` on a
`Char`). Lemma names can be guessed from the statement:
`(m.insert key v).get other` with `other ≠ key` is `Map.getInsertOther`,
and the `↔` form of a membership fact is the bare name
(`List.memFilterMap`), with `Intro` and `Elim` for its two directions.

**The recommendation.**

1. Write down the lemma scheme std mostly follows already (§1): name the
   conclusion, outermost function first; the bare name of a
   membership-style fact is its `↔`; `Intro`/`Elim` are its halves; `Of`
   names a hypothesis; a constructor after a function names the argument's
   shape, unless the function has no argument of that type, when it names
   the result in a hypothesis; `Eq` plus a constant (`EqZero`, `EqNil`,
   `EqSome`) names the result in the conclusion. The 75 SW-2159 lemmas take
   their names from it (§1.6).
2. Settle 21 functions with more than one name, the wrong home or a
   misleading argument order (§2), with no aliases. About 1,700 sites
   change, most of them `rangeFrom` (380, an argument swap), `getOrElse`
   (200) and the `Parse` character tests (180).
3. Rename the function `List.distinct` to `List.unique`, so `distinct` in a
   name always means the proposition `List.Distinct` (§3, D3150).
4. Eight lanes (§5): five DeepSeek, one Sonnet for the `Text` natives, one
   Opus for the `rangeFrom` swap (omega and the unifier read its argument
   positions), and one Opus audit for the older lemma names.

**D questions:** D3150 (`List.distinct` → `List.unique`) and D3151
(`Set.min` → `Set.minimum`). Everything else is decided below under
"Calls I made".

## 1. The naming scheme for lemmas

### 1.1 The problem

A user proving something about `List.filter` wants the fact that `x` is in
`xs.filter p` exactly when `x ∈ xs` and `p x`. Today the obvious guess,
`List.memFilter`, is only the forward half (`List/Lemmas.sw:1103`), and
the backward half is `List.memFilterIntro` (`List/Lemmas.sw:2404`). For
`List.map`, it's the other way round: the bare `List.memMap` is the
backward half (`List/Lemmas.sw:1064`) and the forward half is
`List.memMapElim` (`:1099`). For `flatMap` and `filterMap`, the bare name
is the `↔` (`List/Lemmas.sw:1153`, `:2497`), with `Intro` and `Elim`
beside it (`:1137`). Three conventions in one file: the user has to look
each one up.

The SW-2159 lanes are about to add 75 lemmas. Without a written scheme,
each lane picks names from whichever neighbour it reads.

### 1.2 What std does today

I read the 2,986 `theorem` names under `crates/elab/src/std/` and sampled
about 60 statements. Most of std already follows one scheme, the one
Lean's core library and Mathlib use (their `mem_map`, `mem_filter`,
`map_map`, `length_append`, `le_of_lt` and so on), translated to
camelCase:

- **The name is the conclusion, outside in.** `List.lengthAppend` is
  `(xs ++ ys).length = …` (`List/Lemmas.sw:5`), `List.mapMap` is
  `(xs.map g).map f = …` (`:790`), `List.filterFilter` (`:474`),
  `Map.getInsert` (`Map/Map.sw:619`). The relation is a word: `mem` for
  `∈`, `le`, `lt`, `contains`, `distinct`.
- **A different key or index is `Other`,** with an `ne` hypothesis:
  `Map.getInsertOther` (`Map/Map.sw:622`), `Set.containsInsertOther`
  (`Set/Spec.sw:265`), `Array.getSetOther`, and the maps of sets,
  `Map.getInsertInOther` (`Set/Spec.sw:753`). The same-key fact is bare.
  21 names end in `Other`, and all of them mean this.
- **The halves of an `↔` are `Intro` and `Elim`:** `Set.containsInsertElim`
  (`Set/Spec.sw:407`) and `Set.containsInsertIff` (`:418`),
  `List.memFlatMapIntro`/`Elim`, `List.memFilterMapIntro`/`Elim`,
  `List.memDedupIntro`/`Elim`. 18 `Intro` and 20 `Elim`.
- **`Of` names a hypothesis,** as Lean's `_of_` does: `Nat.leOfAddLe`
  (`Nat/Arith.sw:441`), `Nat.mulLeOfLeDiv` (`:250`), `Nat.lessOfCompare`,
  `List.memOfFindMap`. 183 names contain `Of`.
- **`Some`/`None` after a function that returns an `Option` name the
  result in a hypothesis:** `List.findIndexSome` takes
  `found: xs.findIndex p = Some index` and says what `index` is
  (`List/Lemmas.sw:1572`); likewise `List.findSome` (`:1396`),
  `List.minimumSome` and `List.minimumNone` (`:1642`, `:1663`),
  `Set.belowSome` (`Set/Spec.sw:188`).
- **`EqSome`/`EqNone` characterise the result:** `Option.mapEqSome`
  (`Option/Lemmas.sw:140`), `Option.filterEqSome`, `Option.orElseEqSome`.
- **A constructor after a function whose argument has that type names
  the argument's shape:** `List.lengthCons`, `Nat.iterateSucc`
  (`Nat/Iterate.sw:14`), `Option.orElseNone` (`orElse x None = x`,
  `Option/Lemmas.sw:131`), `List.distinctNil`. `Snoc` is `xs ++ [y]`.
- **Algebra words as in Lean:** `Comm`, `Assoc`, `Cong`, `Mono`, `Self`
  (`Nat.absDiffSelf`), `Left`/`Right` (`Nat.leMaxLeft`), `Pos`, `Ext`,
  `Injective`.
- **`Example`** ends a worked instance that is there as documentation.

Where std breaks this, it does so in a few ways:

| Name | Statement | What's wrong |
| --- | --- | --- |
| `List.memMap` (`List/Lemmas.sw:1064`) | `x ∈ xs → f x ∈ xs.map f` | a half, but bare |
| `List.memFilter` (`:1103`) | `x ∈ xs.filter p → x ∈ xs ∧ p x` | a half, but bare |
| `List.countNone` (`:483`), `List.filterNone` (`:1118`), `List.occurrencesNone` (`:762`) | "no element passes" → `= 0` / `= []` | `None` is neither an argument nor a result here |
| `List.transposeNone` (`:186`) | `transpose [] = []` | the argument is `Nil` |
| `List.memContains` (`:1925`) | `xs.contains x = True ↔ x ∈ xs` | named after both sides; the head is `contains` |
| `Set.isSubsetSpec` (`Set/Spec.sw:380`), `List.allDistinctCorrect` (`List/Distinct.sw:269`), `List.inRangeIff` | a `Bool` test `= True ↔` its proposition | three suffixes for one kind of fact |
| `Set.extIff` (`Set/Spec.sw:404`) | an `↔` hypothesis gives `s = t` | not an `↔` |
| `List.distinctIsDistinctEq` (`List/Distinct.sw:124`) | `distinct xs = distinctEq xs` | `Is` appears nowhere else |
| `List.distinctSnoc` (`List/Distinct.sw:217`) | about the function `List.distinct` | the word means the proposition elsewhere (§3) |

### 1.3 Two designs

**A. Conclusion first, bare `↔` (Lean's scheme; what std mostly does).**
The bare name of a fact is the most complete statement about its left
side: an equation if there is one, an `↔` if not. One-way halves of an
`↔` get `Intro` (the left side is the conclusion) or `Elim` (it is the
hypothesis). A one-way fact that isn't half of a natural `↔`, such as
`List.distinctMap` (`Distinct xs` and `f` injective give
`Distinct (xs.map f)`, `List/Lemmas.sw:1160`), keeps the bare name.

**B. The most-used direction is bare.** This is what `memMap` and
`memFilter` do. The name a user wants is shorter, but which direction is
"most used" is a judgement made once, by whoever wrote it first, and the
reader can't predict it. Adding the `↔` later needs a new suffix, `Iff`,
and that's how `Set.containsInsertIff` came to sit next to a bare
`Set.containsInsert` that says something else (same key, `= True`).

**Recommendation: A.** It's what most of std already does (the newer
`mem*` families, `memFlatMap`, `memFilterMap`, `memRange` and `memDedup`,
are all this way), and it's Lean's scheme, which the people most likely to write proofs in Stitchwort already know. It costs
renaming the older exceptions (§1.5); B would cost renaming the newer
majority. SW-2180, the research lane on how Lean, Agda, Rocq and Isabelle
name their lemmas, is running beside this one. If it finds a reason to
depart from Lean's scheme, the rules below are the place to change.

### 1.4 The rules

1. **Name the conclusion, outside in.** Each function in the conclusion's
   left side, outermost first, as written in std: `getInsertOther` is
   `get (insert m key v) other`. A relation is a word: `mem` (`∈`), `le`
   (`≤`), `lt` (`<`), `contains`, `distinct`, `sorted`. An equation
   between two operations is the two names, left then right, with nothing
   between: `List.concatMapFlatMap`, `List.maximumOfMap`.
2. **The bare name is the full statement:** an equation if there is one,
   else the `↔`. The halves of an `↔` are `Intro` (proves the left side)
   and `Elim` (uses it), even if the `↔` itself isn't in std yet.
3. **A one-way fact that isn't half of a natural `↔` keeps the bare
   conclusion name** (`distinctMap`, `sumByLe`). If two such facts share a
   conclusion, the second adds `Of` and its distinguishing hypothesis.
4. **`Of` names a hypothesis**, the head of the hypothesis that matters:
   `leOfAddLe`, `memOfFindMap`. Leave out a predicate the hypothesis
   shares with the conclusion: `List.distinctOfMap`, not
   `distinctOfDistinctMap` (Lean's `Nodup.of_map`).
5. **When the conclusion has no head of its own** (a conjunction of facts,
   an `∃`, `Void`, or a continuation's `goal`), name the hypothesis
   instead: `findSome`, `minimumNone`, `memMapElim`.
6. **Constructors.** After a function that takes an argument of that type,
   a constructor names the argument's shape: `lengthCons`, `iterateSucc`,
   `orElseNone`, `addZero`. After a function with no such argument, `Some`
   and `None` name its result in a hypothesis: `findSome` means "given
   `find … = Some y`". To say what the result is in the conclusion, write
   `Eq` and the constant: `countEqZero`, `filterEqNil`, `mapEqSome`,
   `sizeEqZeroOfPopMinNone`.
7. **`Other`** is a key or index different from the one the operation
   touched, given by a hypothesis `ne: other ≠ key`; the same-key fact is
   bare. **`Self`** is an operation applied to one value twice
   (`absDiffSelf`). **`Left`/`Right`** say which argument or side.
8. **A `Bool` test and its proposition are bridged by `…Iff`**:
   `f … = True ↔ P`. The bare name is the function itself, so the bridge
   needs a suffix, and it's always `Iff`: `Set.isSubsetIff`,
   `List.isDistinctIff`, `Nat.inRangeIff`, `List.containsIff`. Its halves,
   where they're stated, are `Sound` (`= True` gives `P`) and `Complete`
   (`P` gives `= True`), as `List.allDistinctFromSound` and `Complete`
   are now. `Iff` on any other lemma means rule 2's bare name was taken
   by an equation about the same left side (`Set.containsInsertIff`).
9. **`Spec` and `Correct`.** `Spec` is the full description of a result
   that is not itself a fact about one function (`Map.popMinSpec`, a pair
   and a map). `Correct` is an algorithm proved equal to a reference
   (`Graph.breadthFirstCorrect`, `Nat.sumBetweenCorrect`).
10. **Two predicates or constructors that exclude each other:**
    `aNotB` (`Option.noneNotSome`, and SW-2159's `Char.spaceOrTabNotDigit`).
11. **Namespace:** the type the lemma is about, which is the namespace of
    the conclusion's head, except where that head is a generic relation
    on a converted value (`Set.memToList` is about a set, though `∈` is on
    the list).
12. **A specialisation to one type** lives with the general one and names
    the type at the end only if the general name is taken:
    `Ord.maxNat` (SW-2001).

### 1.5 Existing names to change

These follow from the rules; §5 gives them to lanes. The sample in §1.2
is not exhaustive, so lane O2 audits the rest of the `mem*`, `contains*`
and `get*` families and the `Bool` bridges, and files what it finds.

| Old | New | Sites (std / aoc / rest) |
| --- | --- | --- |
| `List.memMap` | `List.memMapIntro`; the bare name becomes the new `↔` | 22 / 83 / 20 |
| `List.memFilter` | `List.memFilterElim`; bare becomes the `↔` | 12 / 48 / 4 |
| `List.memContains` | `List.containsIff` | 9 / 42 / 0 |
| `List.countNone` | `List.countEqZero` | 3 / 5 / 0 |
| `List.filterNone` | `List.filterEqNil` | 4 / 0 / 0 |
| `List.occurrencesNone` | `List.occurrencesEqZero` | 2 / 2 / 0 |
| `List.transposeNone` | `List.transposeNil` | 1 / 0 / 0 |
| `Set.isSubsetSpec` | `Set.isSubsetIff` | 2 / 0 / 0 |
| `Set.extIff` | `Set.extOfIff` | 2 / 2 / 0 |
| `List.allDistinctCorrect` | `List.isDistinctIff` (with §3) | in §3 |
| `List.distinctIsDistinctEq` | `List.uniqueUniqueDecEq` (with §3) | in §3 |

### 1.6 SW-2159's names against the scheme

Most of the names in `docs/reviews/SW-2159-aoc-lemmas-to-std.md` (§C to
§K) already fit. These change; the lanes use the right-hand names:

| SW-2159 name | Name | Rule |
| --- | --- | --- |
| `List.distinctSnocIntro` | `List.distinctSnoc` (free once §3 renames the function's lemma to `List.uniqueSnoc`) | 3, §3 |
| `List.withIndexDistinct` | `List.distinctWithIndex` | 1 |
| `List.indexFromAbove` | `List.memWithIndexFromLe` | 1 |
| `List.countSplitOn` | `List.countAddCountNot` (no `splitOn` is involved) | 1 |
| `Option.getOrElseMergeAdd`, `Option.getOrElseMap2And` | `Option.getOrMergeAdd`, `Option.getOrMap2And` | §2 |
| `Set.memberOfSizePos` | `Set.containsOfSizePos` (std says `contains`, not `member`) | 1, 4 |
| `Set.sizeOfPopMinNone` | `Set.sizeEqZeroOfPopMinNone` | 6 |
| `Parse.spaceNotDigit` | `Char.spaceOrTabNotDigit` | 10, §2 |
| `Parse.digitNotEq` | `Char.beqFalseOfDigitNotDigit` | 4, §2 |
| `List.sumByRangeFromKeepIf`, `List.rangeFromSplitFirst`, `List.memPairsRangeFrom` | names unchanged; statements take `rangeFrom start count` if lane O1 has merged | §2 |

## 2. Every operation with more than one name

### 2.1 The problem

A user who has written `m.getOr key 0` on a map writes `o.getOr 0` on an
option and gets an error: it's `o.getOrElse 0`, with the same meaning.
They fold a text with `t.fold` and get a right fold, where every other
`fold`-like name in std says which way it goes. `Set.intersect` sits
beside `Set.union` and `Set.difference`. `List.inRange` takes a `Nat`, so
`x.inRange 0 5` isn't found. The S7 review lists these; this section adds
what a wider read found and settles each.

### 2.2 The principles

These decide the cases below, and new names later.

- **P1. One name per operation, the same on every type.** No aliases.
- **P2. A function lives in the namespace of its first explicit
  parameter's type** (its receiver), so that a dot call finds it:
  `Nat.inRange`, `Char.isAsciiDigit`, `List.joinOn` (its receiver is the
  list). Lean and Rust do the same for the same reason.
- **P3. `Bool` tests:** an adjective or noun takes `is` (`isEmpty`,
  `isSubset`, `isDisjoint`, `isDistinct`, `isSome`); a verb doesn't
  (`contains`, `startsWith`, `divides`, `any`, `all`). Rust and Python
  agree (`is_disjoint`, `isdisjoint`, `contains`).
- **P4. A proposition is a capitalised adjective or noun** (`Distinct`,
  `Sorted`, `Disjoint`), and its `Bool` test is `is` plus the same word,
  bridged by an `…Iff` lemma (rule 8).
- **P5. A value fallback is `…Or`** (`getOr`, `headOr`, `errorOr`), as
  `List`, `Array`, `Map`, `Vec` and `NonEmptyList` have it now. `orElse`
  stays for `Option → Option → Option` (Rust's `or`).
- **P6. Set algebra is nouns:** `union`, `intersection`, `difference`
  (Haskell's `Data.Set`, Rust's `HashSet`, Python's `set`); `…With` adds a
  combining function, `…All` folds a list.
- **P7. `min` and `max` are binary; `minimum` and `maximum` are the
  smallest and largest element of a collection** (Haskell's split).
  Compounds keep the short form: `minBy`, `popMin` (Haskell's
  `deleteMin`, Rust's `max_by_key`). D3151 asks about the one place this
  changes something users write.
- **P8. Argument order:** the receiver first; when the receiver is a
  count, the value being threaded comes last, so
  `grid |> Nat.iterate 100 step` pipes; a start comes before a count.
- **P9. `…From`** is the variant with a starting point or a seen set as
  its first argument: `withIndexFrom start`, `findIndexFrom start`,
  `distinctFrom seen`.

### 2.3 The decisions

"Sites" are std / aoc / games, examples / guide (`docs/guide`,
`docs/syntax.md`, `web/guide`) / Rust (including Stitchwort source
embedded in Rust tests). Lemma names that contain the old name are
renamed with it and are counted in the row.

| # | Today | Becomes | Why, and precedent | Sites |
| --- | --- | --- | --- | --- |
| 1 | `Option.getOrElse`, `Result.getOrElse` | `Option.getOr`, `Result.getOr` | P5; every other type's is `getOr`. Rust `unwrap_or`, Lean `getD`; the value is not a thunk, so `OrElse` (Scala's, lazy) misleads | 64 / 109 / 14 / 17 / 10 |
| 2 | `Result.errorOrElse` | `Result.errorOr` | P5, with 1 | 4 / 1 / 0 / 0 / 1 |
| 3 | `Text.fold` (a right fold, `Text/Basics.sw:26`) | `Text.foldRight`, and a new `Text.foldLeft` | P1: every collection has `foldLeft` and `foldRight` (`List/Toolkit.sw:65,80`, `Set/Set.sw:46,99`); `Text.foldChars` becomes `Text.foldRightChars`. `Text.fold` is a compiled native (`core/src/registry.rs:396`, `native/src/n1.rs`), so this is the Sonnet lane | 3 / 0 / 1 / 0 / 48 |
| 4 | `Text.joinWith` (`Text/Basics.sw:174`, list first, `@[noReceiver]`) and `List.joinWith` (`:180`, which calls it) | one function, `List.joinOn` | P1, P2: two definitions of one join; the receiver is the list (Rust's `[S]::join`). `joinOn` pairs with `Text.splitOn`, its inverse (Haskell's `splitOn`/`intercalate` pair, Lean's `splitOn`) | 8 / 8 / 13 / 1 / 6 |
| 5 | `Text.join` (`Text/Basics.sw:162`, list first, `Char` separator) | `List.join` | P2; pairs with `Text.split` on a `Char`, as `joinOn` pairs with `splitOn`. `List.concat` is the flattening join, so there's no clash with Lean's old `List.join`. A native (`registry.rs:402`, `rt/src/prims.rs:704`) | 5 / 2 / 17 / 0 / 53 |
| 6 | `Set.intersect` | `Set.intersection` | P6 | 20 / 17 / 3 / 1 / 1 (`syntax/src/lexer.rs:1212`'s hint for `∩`) |
| 7 | `Map.intersectWith` | `Map.intersectionWith` | P6, with 6; Haskell's `Map.intersectionWith` | 32 / 0 / 0 / 0 / 0 |
| 8 | `NonEmptyList.intersectAll` | `NonEmptyList.intersectionAll` | P6, beside `unionAll` | 8 / 2 / 0 / 2 / 0 |
| 9 | `Set.disjoint` | `Set.isDisjoint` | P3, beside `isSubset`; Rust `is_disjoint`, Python `isdisjoint` | 7 / 5 / 0 / 0 / 0 |
| 10 | `List.inRange (x: Nat) from until` (`List/Toolkit.sw:544`) | `Nat.inRange` | P2. The elaborator builds it for `x in a ..< b` by name (`elab/src/membership.rs:172`), so that string changes too | 19 / 33 / 25 / 11 / 4 |
| 11 | `Parse.isDigit` (`Parse/Parse.sw:227`) | `Char.isAsciiDigit` | P2, and beside `Char.isAsciiLetter`, `isAsciiUppercase` (Rust `is_ascii_digit`). S8 proposed adding `Char.isAsciiDigit`; with this it is a move, not a second name | 49 / 67 / 2 / 0 / 0 |
| 12 | `Parse.isSpace` (`Parse/Parse.sw:230`, space or tab) | `Char.isSpaceOrTab` | P2, and the name says what it accepts, beside `Char.isAsciiSpace` (six characters) and `Char.isWhitespace` (Unicode). S7 suggested `Parse.isSpaceOrTab`; P2 puts it on `Char` | 44 / 21 / 0 / 0 / 0 |
| 13 | `List.elem` (`List/Toolkit.sw:300`, decision procedure last) | deleted | S6: `List.contains` is the same test, with the lemmas; nothing calls `elem` outside examples | 2 / 0 / 3 / 0 / 0 |
| 14 | `List.concatMap` (core, `core/Helpers.sw:8`) and `List.flatMap` (`List/Toolkit.sw:787`) | `List.flatMap` in user code; `concatMap` stays only for the core, with a bridge `List.concatMapFlatMap` | P1. Rust `flat_map`, Lean 4 `flatMap` (renamed from `bind`), and std's own `Option`/`Result`/`NonEmptyList.flatMap`. The core needs a pure version before `List.map` exists, and `elab/src/derive_finite.rs:451` generates calls to it; once D2890's `@[internal]` exists, mark it so | 15 / 11 / 2 / 2 / 8 |
| 15 | `List.rangeFrom (count) (start)` (`List/Toolkit.sw:260`) | `List.rangeFrom (start) (count)` | P8, P9: "range from 5, 3 numbers"; Lean's `List.range' start len`; the other `…From`s take the start first (`withIndexFrom`, `findIndexFrom`). omega (`elab/src/omega.rs:496-615`), the unifier (`unify.rs:244,1280`) and `congruence.rs` read its arguments by position, so this is an Opus lane | 172 / 167 / 20 / 4 / 15 |
| 16 | `Nat.firstFrom (passes) (count) (start)` | `Nat.firstFrom (passes) (start) (count)` | P8, with 15, which it mirrors | 41 / 3 / 3 / 2 / 0 |
| 17 | `Nat.iterateUntilStable (x) (step) (measure) (shrinks)` (`Nat/Iterate.sw:41`) | `Nat.iterateUntilStable (step) (measure) (shrinks) (x)` | P8, S13: the seed last, as in `Nat.iterate (count) (step) (seed)`, so `grid \|> Nat.iterateUntilStable step size proof` pipes. SW-2148's `iterateUntilStableWithin` takes `(fuel) (step) (x)` | 15 / 0 / 2 / 0 / 0 |
| 18 | `List.distinct` and its family | `List.unique` (§3) | D3150 | §3 |
| 19 | `List.allDistinct` (`List/Distinct.sw:235`) | `List.isDistinct`; `allDistinctFrom` → `isDistinctFrom` | P3, P4: the `Bool` test of `List.Distinct` | 25 / 17 / 0 / 3 / 0 |
| 20 | `Set.min`, `Set.max`, `Map.min`, `Map.max` | `Set.minimum`, `Set.maximum`, `Map.minimum`, `Map.maximum` (lemmas `minToList` → `minimumToList` and so on) | P7, D3151 | 49 / 1 / 0 / 0 / 0, plus dot calls on sets that the checker will point at |
| 21 | `Vec.ofList (n) (xs): Option (Vec a n)` beside `Vec.fromList (xs)` | `Vec.fromListChecked`; `Vec.ofListDec` → `Vec.fromListCheckedDec` | P1: `of` and `from` are one word in std (`fromList` on every collection); `Checked` as in `Int.toNatChecked` | 10 / 4 / 1 / 0 / 2 |
| 22 | `List.memContains` and the other §1.5 lemma names | §1.5 | the scheme | §1.5 |
| 23 | `Text.split`/`Text.splitOn` | unchanged | Two operations, one on a `Char` and one on a `Text`, as Lean has `String.split` and `String.splitOn`; 4 and 5 make the joins match them | — |

### 2.4 Checked and left alone

- **`length` and `size`** (`List`, `Text`, `NonEmptyList`, `Vec` against
  `Array`, `Map`, `Set`). S7 is right that this is common practice (Rust
  has `len` everywhere, but Haskell, Lean and Scala split it this way),
  and both words are what a newcomer types first.
- **`Text.repeat text count` and `List.replicate count x`.** Not the same
  operation: `replicate` makes a list of copies of an element, `repeat`
  joins copies of a text (for a list that's `List.replicate n xs |>
  .concat`). Rust has `str::repeat` beside `vec![x; n]` for the same
  reason.
- **`List.maxBy` and `List.maximumOf`.** Different operations (the
  element with the largest key, the largest key), both documented
  (`List/Toolkit.sw:659`). `maxBy` follows P7's compound rule.
- **`List.nonEmpty` (an `Option NonEmptyList`) and `List.toNonEmpty`
  (with a proof).** Haskell's `nonEmpty :: [a] -> Maybe (NonEmpty a)` is
  the precedent, and the two differ in what they need.
- **`List.lookup` (an association list) and `Map.lookupLast`,
  `Map.lookupWith`.** These read a `List (k, v)`, not a `Map`, and the
  word says so; `Map.get` is the map's.
- **`List.dedup`** (`List/Sort.sw:229`), which drops adjacent repeats
  like Rust's `Vec::dedup`. It keeps its name; §3 is why that matters.
- **`List.count` and `List.occurrences`**, which S6 checked: deliberate,
  and bridged.
- **Internal helpers** (`filterStep`, `distinctLoop`, `Text.splitCons`)
  are renamed only when the function they serve is; hiding them is
  D2890 (`docs/proposals/private-helpers.md`).

## 3. `List.Distinct` and `List.distinct`

### 3.1 The problem

`List.Distinct xs` is the proposition "no element of `xs` appears twice"
(`List/Toolkit.sw:490`). `List.distinct xs` is the function that drops
repeats (`List/Distinct.sw:23`). Lemma names are camelCase, so both
become `distinct…` at the front of a name. Of the 40 or so `List.distinct…`
lemmas, about 30 are about the proposition, by their names and the
statements I sampled (`distinctMap`, `distinctAppend`, `distinctRange`,
`distinctFilter`, `distinctNil`, `List/Lemmas.sw:1039-1995`), and seven are about the function
(`List/Distinct.sw:124-217`: `memDistinct`, `distinctNoRepeats`,
`distinctOfNoRepeats`, `distinctDistinct`, `distinctAppendSeen`,
`distinctSnoc`, `distinctIsDistinctEq`). So the lemma days need most,
"appending a new element keeps a list distinct", can't be called
`List.distinctSnoc`: that name says the function's `distinct (xs ++ [y])
= distinct xs ++ [y]` (`List/Distinct.sw:217`). SW-2159 fell back to
`distinctSnocIntro`, which reads as half of an `↔` that doesn't exist.
And `List.distinctDistinct` (the function is idempotent) reads as nonsense.

### 3.2 Four designs

**A. Rename the function to `List.unique`.** `xs.unique` keeps the first
of each value, in order. `distinctEq` (the `DecEq` version) becomes
`uniqueDecEq`, `distinctFrom` becomes `uniqueFrom`, and the seven lemmas
become `memUnique`, `distinctUnique` (was `distinctNoRepeats`: `Distinct
xs.unique`), `uniqueOfDistinct`, `uniqueUnique`, `uniqueAppendSeen`,
`uniqueSnoc` and `uniqueUniqueDecEq`. Every `distinct` in a name then
means the proposition, and `List.distinctSnoc` is free for the lemma days
need. Precedent: Rust's itertools `unique()` (first occurrence kept, in
order, exactly this), Ruby's and Elixir's `uniq`, lodash's `uniq`. Cost:
`.distinct` is the name Kotlin, Scala, Java streams, C#'s LINQ and SQL
use, so some users will try it first (and get "no `List.distinct`"; the
error's suggestion list should then offer `unique`). Some people read
"unique elements" as "elements that occur once"; the doc's example
(`[3, 1, 3, 2, 1].unique` is `[3, 1, 2]`) settles it. Sites: 34 / 19 / 4
/ 0 / 10 for `distinct`, plus 25 for `distinctEq` and 19 for
`distinctFrom`, nearly all in std.

**B. Rename the proposition to `List.NoDup`** (Lean and Mathlib's
`Nodup`). Lemma names become `noDupMap`, `noDupSnoc`. The function keeps
its familiar name. Cost: about 300 statement sites (86 / 105 / 6 / 62 /
43), and statements read worse: `List.NoDup (xs.map key)` against
`List.Distinct (xs.map key)`; proofs are where the word is read most.

**C. Rename the function to `List.dedup`** (Mathlib's name), and today's
adjacent `List.dedup` to `List.dedupAdjacent`. Cost: Rust's `dedup`
means adjacent repeats, so the Rust reading of `dedup` would be wrong,
and the existing `List.dedup` lemmas (`sortedDedup`, `memDedupIntro`)
change meaning under the same name.

**D. Keep both names, and say in a convention which lemma is which.**
Nothing in a name like `distinctAppend` can tell the reader, so the
convention would be "look at the statement", which is the problem.

**Recommendation: A (D3150).** It changes the fewest user-written sites
(about 25 calls in AoC, against about 110 statements for B), it makes
the common word mean the proposition, which is how a mathematician uses
it ("pairwise distinct"), and it has a precedent with exactly this
behaviour. With A, `List.allDistinct` becomes `List.isDistinct` (§2 row
19) and `allDistinctCorrect` becomes `isDistinctIff`, so the
proposition, its test and the bridge share one word.

## 4. `Set.min` or `Set.minimum`

S7 recommended leaving `List.minimum` against `Set.min`, since `Ord.min`
and `Nat.min` are binary. That leaves two names for "the smallest element
of a collection", which SW-2006 asks to end. Either way is defensible:

- **`minimum` for collections** (Haskell). Renames `Set.min`, `Set.max`,
  `Map.min`, `Map.max` and their lemmas: about 50 sites, nearly all in
  std, plus a few `.min` dot calls on sets in AoC. `min` keeps one
  meaning, binary.
- **`min` for everything** (Rust's `Iterator::min` beside `Ord::min`, and
  Lean 4, which renamed `List.minimum?` to `List.min?`, as far as I
  know). Renames `List.minimum`, `maximum`, `minimumOf`, `maximumOf`,
  `NonEmptyList.minimum`… and their lemmas: about 250 sites, and `xs.min`
  on a list beside `a.min b` on a number.

I recommend `minimum` (D3151): fewer sites, and `min` stays one thing.

## 5. Lanes

Every lane renames with no alias left behind, in std, `aoc/`, `games/`,
`examples/`, `docs/guide/` (with its examples), `docs/syntax.md`,
`web/guide/`, and Stitchwort source embedded in Rust tests (`grep -rn
OLDNAME crates --include='*.rs'`). It leaves `docs/proposals/`,
`docs/reviews/`, `docs/research/` and `aoc/NOTES-*.md` alone: they are
records of what was true. A missed call site doesn't check, so the
checker finds what grep misses.

Every lane runs, and shows the result of:

- `nix develop -c task snap:hashes` (std changes: without `NAME`), then
  `nix develop -c task test:one -- hash_stability`;
- `nix develop -c task test:one -- bound_to_the_prelude` when it edits a
  file under `std/core/` or a definition a native is bound to;
- `nix develop -c task test:one -- the_guide_` when it touches the guide
  or `web/guide`;
- `nix develop -c task test:one -- <name>` for each Rust test file whose
  embedded source it changed;
- `nix develop -c task audit:touched -- <Namespace> …` with every std
  namespace it changed and every AoC day or `Rogue` module whose code
  changed, in one call, in the background. If that would run past two
  minutes, it runs the std namespaces and lists the rest for the
  verifier.

Each DeepSeek brief also has CLAUDE.md's three lines: never run a command
in the background but wait for it (the audit is the one exception the
orchestrator runs itself, if DeepSeek can't); run every test you add and
show it passing; finish with a report of what you changed, each command
and its result, and what you were unsure of.

**Order.** N1 before SW-2159's lane O (which adds `getOr…` lemmas); N4
before SW-2159's L1 (which adds `List.distinctSnoc`). O1 last: it's the
largest and touches tactics. N2's `minimum` part waits for D3151 and N4
for D3150; the rest can start now. N1 to N5 touch many of the same AoC
files but different lines; run two at a time at most, and merge each
before the next starts in the same std file.

### N1. Fallbacks, `iterateUntilStable`, `concatMap` (DeepSeek, 45 min)

> Rename `Option.getOrElse` and `Result.getOrElse` to `getOr`, and
> `Result.errorOrElse` to `errorOr` (§2 rows 1-2,
> `docs/proposals/std-naming.md`). They are defined in
> `crates/elab/src/std/core/ListOptionPair.sw:73` and `core/Result.sw:13,18`.
> Rename every use, qualified and dot (`.getOrElse`), and every lemma whose
> name contains `GetOrElse`. Reorder `Nat.iterateUntilStable`'s parameters
> to `(step) (measure) (shrinks) (x)` (`Nat/Iterate.sw:41`) and every call,
> lemma statement and doc. Replace `List.concatMap` with `List.flatMap`
> everywhere outside `std/core/`, `Fin/Fin.sw` and `derive_finite.rs`; add
> `theorem List.concatMapFlatMap (xs: List a) (f: a → List b):
> List.concatMap xs f = List.flatMap xs f` in `List/Toolkit.sw` beside
> `flatMap`, by induction; say in `concatMap`'s doc that it's the core's,
> and to use `flatMap`. Expected 220 sites. Tests as in §5, with
> `bound_to_the_prelude`.

### N2. Sets and maps (DeepSeek, 45 min; the `minimum` half after D3151)

> Rename `Set.intersect` → `Set.intersection`, `Map.intersectWith` →
> `Map.intersectionWith`, `NonEmptyList.intersectAll` →
> `NonEmptyList.intersectionAll`, `Set.disjoint` → `Set.isDisjoint`, with
> the lemmas whose names contain them (`Set.containsIntersect`,
> `containsIntersectIff`, `Map.getIntersectWith`,
> `NonEmptyList.intersectAllReduce`, …), and the hint in
> `crates/syntax/src/lexer.rs:1212`. Rename `Set.isSubsetSpec` →
> `Set.isSubsetIff` and `Set.extIff` → `Set.extOfIff`. If D3151 is yes:
> `Set.min`/`max` and `Map.min`/`max` → `minimum`/`maximum`, and their
> lemmas (`Set.minToList` → `Set.minimumToList`, `Set.minLeast`,
> `Set.minOfContains`, `Set.missingOfMinNone` → `…MinimumNone`, …);
> `popMin` keeps its name. Rename `Vec.ofList` → `Vec.fromListChecked`
> and `Vec.ofListDec` → `Vec.fromListCheckedDec`. Expected 200 sites.

### N3. Character tests and `inRange` (DeepSeek, 50 min)

> Move `Parse.isDigit` to `Char.isAsciiDigit` and `Parse.isSpace` to
> `Char.isSpaceOrTab` (`Parse/Parse.sw:227,230`), defined in
> `Char/` beside `Char.isAsciiLetter`, and update every use (190 sites;
> the `Parse` combinators that use them too). If S8's lane E has already
> added a `Char.isAsciiDigit`, keep that one and delete `Parse.isDigit`.
> Move `List.inRange` to `Nat.inRange` (`List/Toolkit.sw:544`), with
> `List.inRangeIff` → `Nat.inRangeIff`, and change the name the
> elaborator builds in `crates/elab/src/membership.rs:162,172` (and its
> doc at `:14-15`) to `Std.Nat.inRange`. Delete `List.elem`
> (`List/Toolkit.sw:300`) and change its three uses in `examples/` to
> `List.contains`. Tests as in §5, and `task test:lane AREA=elab` for the
> membership change.

### N4. `unique` and `isDistinct` (DeepSeek, 45 min; after D3150)

> Rename the function `List.distinct` → `List.unique`, `List.distinctEq`
> → `List.uniqueDecEq`, `List.distinctFrom` → `List.uniqueFrom`,
> `List.distinctLoop` → `List.uniqueLoop`, and the function's lemmas in
> `List/Distinct.sw` as listed in `docs/proposals/std-naming.md` §3.2 A
> (`memDistinct` → `memUnique`, `distinctNoRepeats` → `distinctUnique`,
> `distinctOfNoRepeats` → `uniqueOfDistinct`, `distinctDistinct` →
> `uniqueUnique`, `distinctAppendSeen` → `uniqueAppendSeen`,
> `distinctSnoc` → `uniqueSnoc`, `distinctIsDistinctEq` →
> `uniqueUniqueDecEq`, and the `distinctFrom…`/`memDistinctFrom…`
> lemmas). Don't touch `List.Distinct` or any lemma about it
> (`distinctMap`, `distinctAppend`, …): check each `distinct…` name's
> statement before renaming it. Rename `List.allDistinct` →
> `List.isDistinct`, `allDistinctFrom` → `isDistinctFrom`,
> `allDistinctCorrect` → `isDistinctIff`, and the `allDistinctFrom…`
> lemmas. Update the comments that name them in
> `crates/js/src/lib.rs:2588` and `crates/driver/src/search_at.rs:1252`.
> Expected 180 sites.

### N5. Lemma names by the scheme (DeepSeek, 45 min)

> Apply `docs/proposals/std-naming.md` §1.5: `List.memMap` →
> `List.memMapIntro` and `List.memFilter` → `List.memFilterElim`, then add
> the `↔`s under the bare names, from the halves:
> `theorem List.memMap (f: a → b) (y: b) (xs: List a): (y ∈ xs.map f) ↔
> (∃ (x: a) => x ∈ xs ∧ f x = y)` (from `memMapIntro` and `memMapElim`)
> and `theorem List.memFilter (xs: List a) (p: a → Bool) (x: a): (x ∈
> xs.filter p) ↔ (x ∈ xs ∧ p x = True)`. `List.memContains` →
> `List.containsIff`, `countNone` → `countEqZero`, `filterNone` →
> `filterEqNil`, `occurrencesNone` → `occurrencesEqZero`, `transposeNone`
> → `transposeNil`. Expected 230 sites, most of them `memMap` and
> `memFilter` in AoC proofs; check that each old `memMap` use gets
> `memMapIntro`, not the new `↔`.

### S1. The `Text` natives (Sonnet, 60 min)

> `Text.fold` → `Text.foldRight` (and `Text.foldChars` →
> `Text.foldRightChars`), plus a new `Text.foldLeft (text) (initial) (f:
> b → Char → b)` with a lemma tying it to `List.foldLeft` on
> `text.toList`; `Text.join` → `List.join`; `Text.joinWith` and
> `List.joinWith` → one `List.joinOn (texts: List Text) (separator:
> Text)` with no `@[noReceiver]`; `Text.joinSplit` and the lemmas follow.
> `Text.fold` and `Text.join` are bound in `crates/core/src/registry.rs:396,402`
> and compiled in `crates/native/src/n1.rs` and `crates/rt/src/prims.rs`;
> rename the registry strings and check the natives still bind
> (`bound_to_the_prelude`, `pinned_hashes`, `task test:lane AREA=native`
> and `AREA=rt`). Decide whether `Text.foldLeft` gets a native too, and
> say so; without one it runs as `List.foldLeft` on the characters.

### O1. `rangeFrom` and `firstFrom`: start before count (Opus, 75 min, last)

> Swap `List.rangeFrom`'s parameters to `(start) (count)` and
> `Nat.firstFrom`'s to `(passes) (start) (count)`, with every call,
> statement and lemma (380 and 50 sites; lemma names don't change). omega
> reads `rangeFrom`'s arguments by position (`crates/elab/src/omega.rs`
> around `:496-615`, `memRangeFrom x c s`), the unifier solves its
> arguments by a special case (`unify.rs:244`, `:1280`), and
> `congruence.rs:15-18` describes the shape `List.range` unfolds to; all
> three change with it, and their tests run
> (`task test:lane AREA=elab`, the omega and unify tests by name). Name
> the arguments at call sites in program code (`List.rangeFrom (start :=
> 1) (count := size)`), not in proofs.

### O2. Audit the remaining lemma names (Opus, 45 min, read only)

> Read every `mem*`, `contains*`, `get*` lemma and every `Bool` bridge
> (`…Spec`, `…Correct`, `…Iff`, `…Sound`, `…Complete`) in
> `crates/elab/src/std/` against the rules in
> `docs/proposals/std-naming.md` §1.4, and list each that breaks one, with
> its statement, the rule and the new name, as
> `docs/reviews/SW-N-lemma-names.md`. Then file the renames as one or two
> DeepSeek lanes like N5.

## 6. Calls I made

- **The note decides all but two rows itself.** These are reversible
  renames that follow from P1 to P9; only the two where a reasonable
  person would choose the other way (§3, §4) go to Matt.
- **No aliases, and no deprecation period** (SW-2006, D2858): the
  checker finds every missed site, and the only users are in this repo.
- **Records keep the old names.** Reviews, proposals, research notes and
  the AoC friction notes say what was true when they were written.
- **`Char.isSpaceOrTab`, not `Parse.isSpaceOrTab`** (S7's suggestion):
  P2 puts a character test on `Char`, where `c.isSpaceOrTab` finds it.
- **`List.joinOn`, not `Text.joinOn`** (S7's suggestion): the receiver is
  the list, and keeping a second, `@[noReceiver]` copy in `Text` is the
  duplication SW-2006 removes.
- **The `rangeFrom` swap goes ahead,** although it's the costliest
  item, because migration cost doesn't count and the swap removes a
  misreading in about 200 proof lines a user reads. It's Opus because
  omega and the unifier depend on the order.
- **`Text.split`/`splitOn`, `length`/`size`, `Text.repeat`,
  `maxBy`/`maximumOf`, `nonEmpty`/`toNonEmpty` and `List.dedup` stay,**
  for the reasons in §2.4.
- **`concatMap` stays in the core** until D2890's `@[internal]` can hide
  it: the core needs a pure version before `List.map`, and generated
  `Finite` instances call it.
- **The `DecEq` version of `unique` is `uniqueDecEq`.** `uniqueEq` would
  read as an equation under rule 1, and `By` means a key function in std
  (`sortBy`, `groupBy`).
- **SW-2159's renamed lemmas** (§1.6) are this note's to set; the lanes
  that add them use the new names, whichever lane merges first.

## 7. D questions

- **D3150:** Rename the function `List.distinct` to `List.unique` (and
  `distinctEq` to `uniqueDecEq`), so that `distinct` in a lemma name
  always means the proposition `List.Distinct`, and `List.distinctSnoc`
  can be the lemma days need? [rec: yes: about 25 AoC calls change
  against about 110 AoC statements for renaming the proposition instead,
  the word keeps its mathematical meaning in proofs, and itertools'
  `unique()` behaves exactly like ours.]
- **D3151:** Rename `Set.min`/`max` and `Map.min`/`max` to `minimum`/
  `maximum`, so the least element of a collection has one name and `min`
  is always binary? [rec: yes: about 50 sites, nearly all in std,
  against about 250 for moving lists to `min`; S7 had recommended
  leaving it, but SW-2006 asks for one name.]

## 8. Tickets to file

| Lane | Model | Estimate | Tests | Order |
| --- | --- | --- | --- | --- |
| N1 fallbacks, `iterateUntilStable`, `concatMap` | DeepSeek | 45 min | §5, with `bound_to_the_prelude` | now; before SW-2159 lane O |
| N2 sets and maps (+ `minimum` after D3151), `Vec.fromListChecked` | DeepSeek | 45 min | §5 | now (the `minimum` part after D3151) |
| N3 `Char` tests, `Nat.inRange`, delete `List.elem` | DeepSeek | 50 min | §5, `test:lane AREA=elab` | now; coordinate with S8's lane E |
| N4 `unique`, `isDistinct` | DeepSeek | 45 min | §5 | after D3150; before SW-2159 L1 |
| N5 lemma names (§1.5) | DeepSeek | 45 min | §5 | now |
| S1 `Text` natives: `foldRight`/`foldLeft`, `List.join`, `List.joinOn` | Sonnet | 60 min | §5, `bound_to_the_prelude`, `pinned_hashes`, `test:lane AREA=native`, `AREA=rt` | now |
| O1 `rangeFrom`/`firstFrom` start first | Opus | 75 min | §5, `test:lane AREA=elab`, omega and unify tests by name | last |
| O2 lemma-name audit | Opus | 45 min | none (read only) | any time; its renames after N5 |

- **SW-2006** is replaced by N1 to N5, S1 and O1; close it when they're
  filed.
- **SW-2177** is answered by §3 and done by N4.
- **S6's `List.elem` and `concatMap` items** had no ticket (SW-2001, lane
  A, took only S2 and S9); N1 and N3 take them.
- **SW-2148** (`iterateUntilStableWithin`) should take its arguments as
  `(fuel) (step) (x)`, per row 17; add that to its body.
- **SW-2159's briefs** should point at §1.4 and use §1.6's names.
- **S8's lane E** should not add `Char.isAsciiDigit` separately if N3
  runs first.
- A small follow-up for the error message: when `xs.distinct` (or
  another old name) isn't found, the suggestions should offer the new
  name. Worth checking whether the existing "did you mean" already does
  this by edit distance (it wouldn't for `distinct` → `unique`).
