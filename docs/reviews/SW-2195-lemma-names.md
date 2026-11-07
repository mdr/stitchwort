# SW-2195: std lemma names against the naming scheme

Lane O2 of `docs/proposals/std-naming.md` (SW-2179). Read only, 7 November
2026, at `87ec3db19`. Nothing was built or run; the checks are Python scripts
over the source text (below). The rules are §1.4 of the proposal, cited as
"rule N". Use counts are qualified-name occurrences, written std / aoc /
games+examples / docs (guide, syntax, web guide; not proposals, reviews or
research) / Rust, with the definition itself left out.

## Summary

Std's names are in better shape than the 55-against-53 `less`/`lt` count
suggests. Of the 2,986 theorems, about 150 break a rule, and most of them
come in a handful of patterns that a mechanical sweep can fix. Half the
`less` names are correct already: 26 of the 55 name the constructor `Less` or
the `Bool` functions `Int.less`, `Float.less` and `Ordering.isLessEq`, not
`<`. So 29 need to change, not 55. There are 20 true duplicates (the same
statement under two names). Sixteen of them are copies of `Bool`, `Ordering`
and `Nat` facts in `Float.Theory`, `Ring` and `Omega`, which I take to be
there because those files were written apart from the rest. The audit also
found five places where §1.4 is silent or would give the wrong answer. The
biggest is that rule 1 as written ("outermost first") would rename
`zeroAdd` and `takeAppendDrop`, which follow Lean's reading of infix
operators left to right.

**Top five recommendations.**

1. **Rename the 29 `less` names that mean `<` to `lt`** (§1), in lanes L1 to
   L3. Six of them are names the elaborator builds terms with (`Nat.lessLe`,
   `Nat.lessTrans`, `Nat.lexSecondLess`, `Nat.leqFalseOfLess`, and the core
   registry), so that part goes to a Sonnet lane. This waits on D3160 (`lt`
   over `less`, `docs/research/std-lemma-libraries.md` §7), which is already
   open.
2. **Delete the 20 duplicates** (§6). Among them: `Nat.modLess` goes in favour
   of `Nat.modLt` (it has the `auto` premise), `Float`'s nine `Bool`
   copies go, and `List.memOfAll` (core) and `List.allMem` become one lemma.
3. **Put the conclusion first in the 36 `List` lemmas whose names start with
   the operation** (`sortLength`, `permLength`, `mergeMap`, `getSomeLt`, …;
   §2) and fix the `mem*` halves (§4), in lane L4, after N4 and N5.
4. **Add five clarifications to §1.4** (§7): the infix reading; what to do
   when a two-word compound is already a function's name (`filterOfMap`
   against `List.filterMap`); one word for "an operation keeps a membership"
   (`…OfContains`, not `Keeps` or `Mono`); `False`/`True` results take no
   `Eq`; and one way to state an `Elim` (`∃` or `List.Any`).
5. **Give O1 the `memRangeFrom` family and the four `sumRange…None` lemmas**
   (§5). omega reads `memRangeFrom`, `memRangeFromOf`, `memRangeBounds` and
   `memRangeOf` by name (`crates/elab/src/omega.rs:492-516`), and O1 rewrites
   those statements and that code anyway.

**Counts.** Renames proposed: 118 names in six groups (L1 to L5, plus 8
added to O1), about 700 sites: 411 in std, 167 in AoC, 41 in games and
examples, 45 in docs and 31 in Rust. Duplicates: 20 lemmas to delete. Rule
clarifications: 5. D questions: none. The one direction choice here, `lt`
over `less`, is D3160.

## Method

- `extract.py` read every `theorem` header under `crates/elab/src/std/`
  (2,986, which matches the proposal) with its statement up to the top-level
  `:=` or the first match clause. `uses.py` counted each qualified name, and
  its `Std.`-prefixed form, across `crates/elab/src/std`, `aoc/` (without
  `NOTES-*.md`), `games/`, `examples/`, `docs/` with `web/guide`, and
  `crates/**/*.rs`.
- **Duplicates** (`dups2.py` to `dups4.py`) were found by parsing each
  statement into binders, hypotheses and a conclusion, then comparing them in
  four ways: with binder names erased; also ignoring `auto`; also ignoring
  argument order and which way round `=`/`≠` is; and also equating
  `Nat.leq … = True` with `≤`, `Nat.LessThan` with `<`, `List.Mem` with `∈`,
  `Nat.equal` with `==`, and `(h: P): Void` with `¬P`.
- **Order** (`order.py`) found theorems whose conclusion's left side is headed
  by `f` while the name has `F` somewhere other than the front. I read all 77
  hits; about 40 are real (§2), and the rest are infix readings or misparsed
  dot chains.
- I read every `less`/`lt` name (108), every `mem*`/`contains*` name (126),
  every `get*` name (175), every name with a `Spec`, `Correct`, `Iff`,
  `Sound` or `Complete` suffix or with a `Bool` `↔` in its statement (59),
  every `Of` name that has no hypothesis, and every `None`/`Some`/`Other`
  name whose statement doesn't contain the word.
- The scripts are in the session scratchpad, not the repo. They could seed
  the research note's duplicate check (ticket T2, §4.3 of
  `std-lemma-libraries.md`).

Not read one by one: the bodies of `Parse/Runs.sw` and `Parse/Reads.sw` (268
theorems), `Float/Theory.sw` (172) and `Map/Spec.sw` (190). They went
through the automated checks only. Most of them are internal steps of larger
proofs.

## 1. `less` for `<`

29 rename, 26 stay. Rule 1's dictionary: `lt` for `<`.

| Old | File | New | Uses | Notes |
| --- | --- | --- | --- | --- |
| `Nat.lessLe` | `core/Division.sw:61` | `Nat.leOfLt` | 19/1/0/2/3 | `derive_induct.rs:336`, `calc.rs:518`, `search_bench.rs:391`: **L1** |
| `Nat.lessTrans` | `core/Division.sw:63` | `Nat.ltTrans` | 4/0/0/6/3 | `core/src/registry.rs:196`, `calc.rs:15,369`: **L1** |
| `Nat.lexSecondLess` | `core/Division.sw:99` | `Nat.lexSecondLt` | 0/0/0/1/1 | `registry.rs:213`: **L1** |
| `Nat.leqFalseOfLess` | `Nat/Arith.sw:333` | `Nat.leqFalseOfLt` | 2/2/2/0/2 | `omega.rs:125,642`: **L1** |
| `Nat.modLess` | `Nat/Arith.sw:173` | deleted, see §6 | 38/17/4/5/3 | three Rust tests' `decreasing :=`: **L1** |
| `Nat.divTenLess` | `Nat/Digits.sw:6` | `Nat.divTenLt` | 10/0/3/1/1 | `rt/tests/it/lower.rs:407`: **L1** |
| `Nat.lessIrrefl` | `Nat/Arith.sw:35` | `Nat.ltIrrefl` | 19/0/0/0/0 | |
| `Nat.leLessSucc` | `Nat/Arith.sw:38` | `Nat.ltSuccOfLe` (Lean's `lt_succ_of_le`) | 1/12/0/0/0 | |
| `Nat.equalOfLess` | `Nat/Arith.sw:604` | `Nat.equalFalseOfLt` (the conclusion is `Nat.equal v b = False`) | 3/0/0/1/0 | |
| `Nat.lessNotLe` | `Nat/Arith.sw:628` | `Nat.leqSuccNotLeq` (a `Bool` equation: `leq (Succ x) u = not (leq u x)`; there's no `<` in it) | 1/2/0/1/0 | |
| `Nat.halvesLess` | `Nat/Bits.sw:51` | `Nat.halvesLt` | 6/0/0/0/0 | |
| `Nat.fromDigitsHeadLess` | `Nat/Digits.sw:135` | `Nat.fromDigitsLeOfHeadLt` (the conclusion is `≤`) | 0/2/0/2/0 | |
| `Nat.headLessArith` | `Nat/Arith.sw:426` | `Nat.headLtArith` | 1/0/0/0/0 | helper |
| `Nat.lessOfCompare` | `core/Compare.sw:96` | `Nat.ltOfCompareEqLess` | 4/2/1/0/0 | rule 6: `Eq Less` is the hypothesis's constant |
| `Nat.compareOfLess` | `core/Compare.sw:102` | `Nat.compareEqLessOfLt` | 4/0/1/0/0 | |
| `Int.lessOfCompare` | `core/Compare.sw:146` | `Int.ltOfCompareEqLess` | 2/0/0/0/0 | |
| `Int.compareOfLess` | `core/Compare.sw:152` | `Int.compareEqLessOfLt` | 2/0/0/0/0 | |
| `Ord.lessLe` | `Ord/Ord.sw:135` | `Ord.leOfLt` | 2/0/4/0/0 | |
| `Ord.lessTrans` | `Ord/Ord.sw:138` | `Ord.ltTrans` | 0/0/1/0/0 | |
| `Ord.leLessTrans` | `Ord/Ord.sw:142` | `Ord.leLtTrans` | 1/0/0/0/0 | |
| `Ord.lessLeTrans` | `Ord/Ord.sw:149` | `Ord.ltLeTrans` | 1/0/0/0/0 | |
| `List.dropConsLess` | `List/Toolkit.sw:574` | `List.lengthDropConsLt` (also out of order) | 1/0/0/0/0 | |
| `Float.Theory.magUnitsLess` | `Float/Theory.sw:246` | `…magUnitsLt` | 6/0/0/0/0 | |
| `Float.Theory.scaledLess` | `:359` | `…scaledLt` | 5/0/0/0/0 | |
| `Float.Theory.halfLess` | `:365` | `…halfLt` | 1/0/0/0/0 | |
| `Float.Theory.cancelLess` | `:629` | `Nat.ltOfMulLtMulRight`, moved to `Nat/Arith.sw` (a plain `Nat` fact: `a * c < b * c → a < b`) | 6/0/0/0/0 | |
| `Float.Theory.scaleLess` | `:650` | `…scaleLt` | 1/0/0/0/0 | |
| `Float.Theory.quotLess` | `:757` | `…quotLt` | 1/0/0/0/0 | |
| `Float.Theory.notLessSelf` | `:369` | deleted, see §6 (`Nat.ltIrrefl`) | 4/0/0/0/0 | |

**Staying, because `less` here is not `<`.**
- The constructor `Ordering.Less`: `Ordering.lessNotEqual`, `lessNotGreater`,
  `equalNotLess`, `greaterNotLess` (rule 10), `Map.Spec.insertWithLess`,
  `removeLess`, `mergeLess`, `lessOfLessLe`, `notLessOfLess`,
  `Map.Tree.lessOfGreater` and `lessOfLeLess`.
- The `Bool` functions `Int.less`, `Float.less`, `Map.Spec.isLess` and
  `Ordering.isLessEq`: `Float.leOfNotLess`, `notLessOfLe`, `keyLessLeq`,
  `Float.Theory.intLessAddPos`, `Omega.intLeqOfLess`, `intLeqOfNotLess`,
  `Map.Spec.isLessSound`, `Ordering.isLessEqIf`, `flipNotLessEq`,
  `notGreaterOfIsLessEq`, `isLessEqOfNotGreater`, `Ord.isLessEqTrans` and
  `isLessEqAntisymm`.

Of these, `Float.keyLessLeq` (`Float/Float.sw:368`) is an `Int` fact in the
`Float` namespace (rule 11). It could be `Int.leqOfLess`, but it has one use.
I've left it.

The 53 `lt` names are all `<`. Three have other problems: `List.getSomeLt`
(§2), and `List.getOrMapLt` and `Vec.getOrShiftLeftLt` (§5).

## 2. The conclusion isn't first (rule 1)

| Old | File | New | Uses |
| --- | --- | --- | --- |
| `List.sortLength` | `List/SortLemmas.sw:1304` | `List.lengthSort` | 2/1/1/1/0 |
| `List.permLength` | `List/Lemmas.sw:720` | `List.lengthEqOfPerm` | 9/6/0/0/0 |
| `List.padRightLength` | `List/Lemmas.sw:166` | `List.lengthPadRight` | 1/1/0/1/0 |
| `List.transposeNLength` | `:190` | `List.lengthTransposeN` | 2/0/0/0/0 |
| `List.transposeLength` | `:297` | `List.lengthTranspose` | 0/0/0/1/0 |
| `List.headsLength` | `:255` | `List.lengthFilterMapGetZero` | 4/0/0/0/0 |
| `List.startsWithLength` | `:625` | `List.lengthLeOfStartsWith` | 1/1/1/0/0 |
| `List.distinctLength` | `:1275` | `List.lengthLeOfDistinct` (rule 4: `Distinct xs` and `xs ⊆ ys` give `length xs ≤ length ys`) | 2/0/0/0/0 |
| `List.subsequenceLength` | `List/SortLemmas.sw:1147` | `List.lengthLeOfSubsequence` | 3/2/0/1/0 |
| `List.all2Length` | `List/Lemmas.sw:2901` | `List.lengthEqOfAll2` | 1/1/0/0/0 |
| `Nat.toBitsLength` | `Nat/Bits.sw:389` | `Nat.lengthToBits` | 7/8/0/0/0 |
| `List.splitAtFst` | `List/Lemmas.sw:2059` | `List.fstSplitAt` | 0/0/0/0/0 |
| `List.mergeMap` | `List/Sort.sw:157` | `List.mapMerge` | 4/0/0/2/0 |
| `List.mergeMapStep` | `:167` | `List.mapMergeStep` | 1/0/0/1/0 |
| `List.mergeRunsMap` | `:185` | `List.mapMergeRuns` | 3/0/0/0/0 |
| `List.sortWithMap` | `:191` | `List.mapSortWith` | 1/0/0/0/0 |
| `List.sortByMap` | `:195` | `List.mapSortBy` | 3/0/0/2/0 |
| `List.sortOnMap` | `List/SortLemmas.sw:1420` | `List.mapSortOn` | 1/2/0/0/0 |
| `List.buildRunsJoined` | `:833` | `List.runsJoinedBuildRuns` | 3/0/0/0/0 |
| `List.buildRunsCount` | `:1286` | `List.runsCountBuildRuns` | 2/0/0/0/0 |
| `List.memLeSumBy` | `List/Lemmas.sw:689` | `List.leSumByOfMem` (Lean's `le_sum_of_mem`) | 1/1/0/0/0 |
| `List.getSomeLt` | `:2662` | `List.ltLengthOfGetSome` | 1/3/0/0/0 |
| `List.getInRange` | `:2649` | `List.isSomeGet`, with the `↔` turned round: `(xs.get k).isSome = True ↔ k < xs.length` (rule 2: the bare name is the `↔` about its left side) | 1/4/0/0/0 |
| `List.findNoneAll` | `:1417` | `List.allOfFindNone` | 1/3/0/0/0 |
| `List.findNotNoneAll` | `:1424` | `List.allOfFindNotNone` | 1/2/0/0/0 |
| `List.findAny` | `:1952` | `List.anyOfFindSome` | 0/0/0/0/0 |
| `List.sortedGetOrLe` | `List/Positions.sw:79` | `List.getOrLeOfSorted` | 4/6/0/1/0 |
| `NonEmptyList.toListToNonEmpty` | `NonEmptyList/Lemmas.sw:27` | `NonEmptyList.toNonEmptyToList`: the statement is `List.toNonEmpty xs.toList = xs`, so the old name reads the composition backwards | 0/0/0/0/0 |
| `Set.popMinNone` | `Set/Spec.sw:148` | `Set.minEqNoneOfPopMinNone` (`minimumEqNone…` after D3151) | 1/1/0/0/0 |
| `Vec.getToList` | `Vec/Vec.sw:281` | `Vec.getOrToList` (the left side is `List.getOr (v.toList) …`) | 2/1/0/0/0 |
| `Bool.decTrueToBool` | `Decidable/Decidable.sw:5` | `Bool.toBoolDecTrue` | 0/0/0/3/3 (`equations.rs:1082,4527`, `module.rs:2863`): **L1** |
| `Nat.decEqFromToBool` | `Nat/Arith.sw:593` | `Nat.toBoolDecEqFrom` | 1/0/0/1/0 |
| `Option.decSomeToBool` | `Option/Lemmas.sw:116` | `Option.toBoolDecSome` | 1/0/0/0/0 |
| `Float.rankIeeeLe`, `rankIeeeLt` | `Float/Float.sw:506,511` | `Float.ieeeLeOfRankLe`, `ieeeLtOfRankLt` | 6, 5 std |
| `Vec.ofListToList`, `ofListDecToList` | `Vec/Vec.sw:189,184` | with N2's rename, `Vec.fromListCheckedSome` and `fromListCheckedDecSome` (rule 6: `Some` names the hypothesis `fromListChecked … = Some v`) | 0/1, 1/0 |

The three `decide`-style names stay in their instance's namespace, not
`Decidable`. Rule 11 would put them in `Decidable`, but users look them up
by the instance's name.

Left alone: `List.gaussSum` (a named theorem, like Lean's), and
`Int.modNatToInt` (`Int/Int.sw:55`, which would be `Int.toIntModNat`, two
uses). The remaining 30-odd hits follow the infix reading (§7 G1):
`Int.zeroAdd`, `Int.oneMul`, `Mod.zeroAdd`, `Text.takeAppendDrop`, the
`Int.…AddSubNatNat` family, `Int.divAddMod…` and `Option.noneOrElse`.

## 3. `Bool` bridges (rule 8)

| Old | File | New | Uses |
| --- | --- | --- | --- |
| `NonEmptyList.containsMem` | `NonEmptyList/Lemmas.sw:139` | `NonEmptyList.containsIff`, like N5's `List.containsIff` | 0/0/0/0/0 |
| `Map.Spec.isLessOf` | `Map/Spec.sw:804` | `Map.Spec.isLessComplete`, beside `isLessSound` | 1/0/0/0/0 |
| `Map.Spec.sameKeyDecide` | `Map/Spec.sw:929` | `Map.Spec.sameKeyBeq` (an equation, `sameKey a b = (b == a)`; rule 1) | 3/10/0/0/0 |
| `Map.memKeysOfContains` | `Map/Map.sw:353` | `Map.memKeysIntro`, the half of the `↔` `Map.memKeys` | 7/3/0/0/0 |

The proposal's own rows, `Set.isSubsetSpec`, `Set.extIff`,
`List.allDistinctCorrect`, `List.inRangeIff` and `List.memContains`, are
right.

**Checked and sound:** `Nat.dividesIff`, `List.allIff`, `List.anyIff`,
`List.anyEqIff`, `Graph.reachableIff`, `Map.Raw.sameSound`/`Complete`/`Iff`,
`Decidable.toBoolSound`, `andBoolSound`, `Omega.checkCertSound`,
`Nat.equalSound`, `Map.Spec.sameKeySound` and `List.allDistinctFromSound`/
`Complete`. The `Set.contains…Iff` family also fits rule 8's last sentence:
each bare name is taken by a `Bool` equation (`Set.containsUnion`,
`containsFilter`, `containsIntersect`, `containsDifference`,
`containsFromList`, `containsInsert`), and the `↔` takes `Iff`.
`Set.containsMap` is bare because it has no equation; that is rule 2, not an
inconsistency. `Option.allFiniteComplete`, `Pair.allFiniteComplete` and
`Fin.allComplete` look like a misuse of `Complete`, but they name the field
`Finite.complete` (`core/Finite.sw:40`, Lean's `Fintype.complete`), so they
stay. Every `Spec` and `Correct` name fits rule 9 (`Graph.*Correct`,
`Nat.sumBetweenCorrect`, `Map.popMinSpec`, `Set.popMinSpec`,
`Nat.partitionPointSpec`, `Float.Theory.*Spec`, `List.mapAccumLeftGoSpec`).

## 4. `Intro`, `Elim` and the bare `mem` names (rules 2-4)

| Old | File | New | Uses |
| --- | --- | --- | --- |
| `List.memAppend` (`x ∈ xs ++ ys → x ∈ xs ∨ x ∈ ys`) | `List/Lemmas.sw:1044` | `List.memAppendElim`; the bare name becomes the new `↔`, from it and `memAppendLeft`/`Right` (`core/Finite.sw:10,16`) | 8/18/3/1/0 |
| `List.memRangeBounds` | `List/Toolkit.sw:524` | `List.memRangeElim` (the bare `List.memRange` is the `↔` already) | 13/2/0/1/2: **O1** |
| `List.memRangeOf` | `:530` | `List.memRangeIntro` | 1/2/0/1/2: **O1** |
| `List.memRangeFrom` (one way, bare) | `:505` | `List.memRangeFromElim`, with a new `↔` `List.memRangeFrom` | 19/13/5/2/2: **O1** |
| `List.memRangeFromOf` | `:537` | `List.memRangeFromIntro` | 0/0/0/0/2: **O1** |
| `List.memTake` | `List/Lemmas.sw:2392` | `List.memOfTake` (rule 4; Lean's `mem_of_mem_take`, without the shared `mem`) | 1/1/0/0/0 |
| `List.memDrop` | `:2398` | `List.memOfDrop` | 1/1/0/0/0 |
| `List.memDedupAfter` | `List/SortLemmas.sw:1427` | `List.memOfDedupAfter` | 3/0/0/0/0 |
| `List.memPerm` | `:891` | `List.memOfPerm` | 4/9/2/0/0 |
| `List.memOfCountPositive` | `List/Lemmas.sw:466` | `List.memOfCountPos` (the word is `Pos`, §1.2) | 1/1/2/0/0 |
| `List.memRemoveFirst` (`y ≠ x → y ∈ ys → y ∈ ys.removeFirst x`) | `List/SortLemmas.sw:1501` | `List.memRemoveFirstOther` (rule 7) | 2/0/0/0/0 |
| `Map.containsInsertSame` | `Map/Map.sw:699` | `Map.containsInsert`, as `Set.containsInsert` (rule 7: the same-key fact is bare) | 4/1/0/0/0 |
| `Map.containsInsertKeeps` | `Map/Map.sw:703` | `Map.containsInsertOfContains` (Lean's `mem_insert_of_mem`) | 3/1/0/0/0 |
| `Set.containsInsertMono` | `Set/Spec.sw:273` | `Set.containsInsertOfContains` | 12/7/0/0/0 |
| `Map.getInsertKeeps` | `Map/Map.sw:652` | `Map.getInsertOfNotContains` | 2/0/0/0/0 |
| `Graph.containsPushedKeeps` | `Graph/Search.sw:182` | `Graph.containsPushEdgesOfContains` | 3/0/0/0/0 |
| `Map.getInsertCases` | `Map/Map.sw:643` | `Map.getInsertEqSomeElim` | 4/1/0/0/0 |

**Checked and sound:** every `Intro`/`Elim` pair in std, including
`memFlatMap`, `memFilterMap`, `memDedup`, `memDistinctFrom` and
`Set.containsInsertElim`. Also sound: the one-way facts whose conclusion has
no head of its own (rule 5: `memZip`, `memPairs`, `memCombinations`,
`memSplit`); the `Of` facts (`memOfGet`, `memOfFindMap`, `Map.containsOfGet`,
`containsOfMemToList`, `Set.containsOfRemove`); and all the `Map`/`Set`/`Vec`
`get…Other` and `contains…Other` names (rule 7 holds for all 21).

**A second spelling of one `Elim`.** `List.memMapAny` (`List/Lemmas.sw:1087`,
14/18/13/1/0) concludes `List.Any (x => f x = y) xs`, and `List.memMapElim`
(`:1099`, 5/60/5/0/0) concludes `∃ x, x ∈ xs ∧ f x = y`: the same fact,
spelled two ways. The siblings disagree too: `memFlatMapElim` and
`memFilterMapElim` use `List.Any`, while N5's new `↔` `memMap` uses `∃`. I
haven't put this in a rename lane, because the fix changes statements. See
§7 G5.

## 5. `Of`, `Other`, `None`/`Some` and `Eq` used for something else (rules 4, 6, 7)

| Old | File | New | Uses |
| --- | --- | --- | --- |
| `Nat.shiftRightNone` (`shiftRight n 0 = n`) | `Nat/Bits.sw:27` | `Nat.shiftRightZero` | 12/1/0/0/0 |
| `Nat.xorSome`, `andSome`, `orSome` (hypothesis `leq (m + n) 0 = False`) | `Nat/Bits.sw:68,174,215` | `Nat.xorOfAddPos`, `andOfAddPos`, `orOfAddPos` | 2, 4, 2 std |
| `List.sumRangeFromNone` | `List/SortLemmas.sw:336` | `List.sumByRangeFromKeepIfEqZero` | 7/4/0/0/0: **O1** |
| `List.sumRangeFromEqNone` | `:379` | `List.sumByRangeFromKeepIfBeqEqZero` | 1/2/0/0/0: **O1** |
| `List.sumRangeNone` | `:394` | `List.sumByRangeKeepIfEqZero` | 0: **O1** |
| `List.sumRangeEqNone` | `:412` | `List.sumByRangeKeepIfBeqEqZero` | 0: **O1** |
| `List.getOfGetOr` (no hypothesis about `getOr`; it's in the conclusion) | `List/Index.sw:71` | `List.getEqSomeGetOr` | 1/1/0/0/0 |
| `List.getOrMapLt` | `List/Index.sw:212` | `List.getOrMapOfLt` (rule 3: the second fact with this conclusion adds `Of` and its hypothesis) | 2/4/0/1/0 |
| `Vec.getOrShiftLeftLt` | `Vec/Grid.sw:55` | `Vec.getOrShiftLeftOfLt` | 1/0/0/1/0 |
| `Map.containsInEq` | `Set/Spec.sw:746` | `Map.containsInGetOr` (after N1). `Eq` + constant means a result (rule 6); this one unfolds a definition | 11/0/0/0/0 |
| `Map.getIndexByEq` | `Map/Map.sw:1001` | `Map.getIndexByBeq` (it's the `==` form of `getIndexBy`) | 5/0/0/0/0 |
| `List.filterOfMap` (no hypothesis) | `List/Lemmas.sw:2413` | see §7 G2 | 2/4/0/1/0 |

Low value, left out of the lanes: `Nat.halfOfDoubleBit` and
`parityOfDoubleBit` (`Nat/Bits.sw:411,420`, where `Of` is English: "half
of"), and `Int.subOfNats` (`Int/Int.sw:152`). `Parse.runsSepByNone`,
`runsWithFinalLineBreakNone` and `runsWithFinalLineBreakSome` use
`None`/`Some` for "zero items" and "without/with the break", a convention
local to `Parse/Runs.sw`. A `Parse` naming pass, if there is one, should
decide it. The only `Other` without a `≠`, `Omega.splitOtherHolds`, names the
function `Omega.Row.splitOther`.

## 6. Duplicates

The same statement under two names, after the normalisation in "Method".
"Keep" is the name the others' uses move to.

| Keep | Delete | Uses of the deleted one | Note |
| --- | --- | --- | --- |
| `Nat.modLt` (`Nat/Arith.sw:219`, `[auto ok: d ≠ 0]`) | `Nat.modLess` (`:173`, explicit `ok`) | 38/17/4/5/3 | callers write `Nat.modLt n d [ok := h]` where `auto` can't find the premise. The three Rust tests with `decreasing := Nat.modLess a b h` change too. The proving guide (`docs/proving-guide.md:237,242,563`) names both. **L1** |
| `Nat.ltIrrefl` (was `lessIrrefl`) | `Float.Theory.notLessSelf` (`Float/Theory.sw:369`, `(h: n < n): Void`) | 4/0/0/0/0 | |
| `Ordering.lessNotEqual` | `Ring.lessNotEqual` (`Ring/Sound.sw:82`) | 2 std | |
| `Ordering.greaterNotEqual` | `Ring.greaterNotEqual` (`Ring/Sound.sw:84`) | 2 std | |
| `Nat.addOne` | `Ring.natAddOne` (`Ring/Sound.sw:42`) | 2/0/0/0/1 | `cli/tests/tools/doc.rs:298` expects it in a list; update the expected list. **L1** |
| `Int.addAddNeg` (`Int/Int.sw:241`) | `Ring.addNegCancel` (`Ring/Sound.sw:32`) | 2 std | |
| `List.allMem` (`List/Lemmas.sw:1387`), moved to core | `List.memOfAll` (`core/ListOptionPair.sw:124`) | 2/0/11/2/3 | the core needs it before `List/Lemmas.sw` loads, so move `allMem` into the core in its place. The argument orders differ (`(p) (xs) (h) (x) (m)` against `(p) (x) (xs) (h) (m)`); keep core's. `derive_induct.rs:25,343,2365` builds terms with it. **L1** |
| — | `Option.memOfAll` (`core/ListOptionPair.sw:130`) has no twin, but its name has the same fault | 0/0/0/2/3 | rename it to `Option.allSome` (rule 6), with `derive_induct.rs:344`. **L1** |
| `Bool.andFalse` (`List/SortLemmas.sw:1306`) | `Float.Theory.andFalseRight` (`:1246`) | 1 | `Bool.andFalse` and `andTrue` sit in `List/SortLemmas.sw`; move them to `Bool/Bool.sw` |
| `Bool.andTrue` (`List/SortLemmas.sw:1310`) | `Float.Theory.andTrueRight` (`:1250`) | 1 | |
| `Bool.andComm` (`Bool/Bool.sw:32`) | `Float.Theory.andSwap` (`:1254`) | 1 | |
| `Or.elim` (`Bool/Bool.sw:90`) | `Float.Theory.orCase` (`:1352`) | 24 std | |
| `Bool.orFalseIntro` (`Bool/Bool.sw:104`) | `Float.Theory.orFalse` (`:1314`) | 2 | |
| `Bool.orFalseLeft` (`:96`) | `Float.Theory.orLeftFalse` (`:1492`) | 1 | |
| `Bool.orFalseRight` (`:100`) | `Float.Theory.orRightFalse` (`:1496`) | 0 | |
| `Bool.notTrue` (`Bool/Bool.sw:122`) | `Float.notTrueFalse` (`Float/Float.sw:405`), `Float.Theory.notTrueFalse` (`:1640`) | 3, 1 | |
| `Int.leqRefl` (new home, rule 11) | `Omega.intLeqRefl` (`Omega/Sound.sw:177`), `Float.Theory.keyRefl` (`:1398`) | 1, 2 | |
| `Option.orElseNone` (`Option/Lemmas.sw:131`) | `Map.orElseNone` (`Map/Map.sw:965`) | 1 | |
| `Bool.eqOf` (`Bool/Bool.sw:63`) | `Quot.boolEq` (`Quot/Quot.sw:60`) | 1 | |

Near-duplicates, kept on purpose:
- `Ordering.thenEqual` (`core/OrdDerived.sw:13`) is `andThenEqual` with
  implicit arguments, a wrapper that `derive_ord.rs:393` applies. Its name
  drops `and`. Making `andThenEqual`'s arguments implicit and deleting the
  wrapper would need `derive_ord.rs` changed. Low value; left.
- Each constructor pair `aNotB`/`bNotA` (`Nat.zeroNotSucc`/`succNotZero`,
  `Option.noneNotSome`/`someNotNone`, …) is both directions on purpose
  (rule 10).
- `Exists.mapExample`/`elimExample` and `List.pairsStep`/
  `Ring.proveNatWithExample` share statements but are examples of different
  things.
- The research note's `natEqSelf`/`Nat.equalRefl` pair: `natEqSelf` isn't in
  std now.
- `List.memMapAny`/`memMapElim`: see §4.

A load-order caution for L3: `Float/Theory.sw` may have its own copies
because `Bool.andFalse` and `andTrue` (in `List/SortLemmas.sw`) weren't
loaded before it. Moving them into `Bool/Bool.sw` first fixes that. The lane
should check the order in `library.rs` (`:1185` describes it) before deleting
anything.

## 7. Gaps in §1.4

- **G1. Infix operators read left to right.** As written, rule 1 ("each
  function in the conclusion's left side, outermost first") makes
  `Int.zeroAdd` (`0 + a = a`) wrong, along with `Text.takeAppendDrop`,
  `List.getOrMem` (`xs.getOr i d ∈ xs`), `Nat.leAddRight` and about 30
  others. They all follow Lean, which reads an infix operator's operands in
  order (`zero_add`, `take_append_drop`). Add to rule 1: "an infix operation
  (`+`, `*`, `++`, `∈`, `≤`, `<`) is read left to right: `zeroAdd` is
  `0 + a`." No renames follow.
- **G2. A compound that is already a function's name.**
  `filter (xs.map g) q` would be `filterMap` by rule 1, but `List.filterMap`
  is a function, and `filterMap…` lemmas are about it. Std wrote
  `List.filterOfMap`, which breaks rule 4. Lean's snake case keeps
  `filter_map` and `filterMap` apart; camelCase can't. Proposed rule: when
  the joined name is a function's, keep the second function's namespace
  word between them (`List.filterListMap`), or make `Of` stand for "of" in
  this one case. **My call:** keep `filterOfMap` and list it in §1.4 as the
  one exception, since it is the only collision I found. `List.all`/
  `List.All` is the same collision as `distinct`/`Distinct`, but there are
  few `All` lemmas, and once `allMem` replaces `memOfAll` (§6) all of them
  read correctly.
- **G3. One word for "an operation keeps a membership".** Std has
  `containsInsertMono`, `containsInsertKeeps`, `getInsertKeeps` and
  `containsPushedKeeps`. Lean's `mem_insert_of_mem` gives
  `containsInsertOfContains`, which rule 4 already produces. Add it to rule 4
  as an example, and §4 renames the four.
- **G4. `False`/`True` results.** Rule 6 says `Eq` + constant names a result
  (`countEqZero`). For `Bool` results std writes the constant alone, 46
  times (`Nat.leqFalse`, `leqSuccSelf`, `equalFalseOfLt`), against 2 with
  `Eq` (`List.anyConsEqTrue`/`False`). Add to rule 6: "for a `Bool` result,
  the constant alone: `leqFalseOfLt`". That is what §1 uses, and no renames
  follow.
- **G5. How an `Elim` is stated.** `memMapElim` gives `∃`, and
  `memFlatMapElim`/`memFilterMapElim` give `List.Any`. The research note's
  rule, "state facts in the spelling user code writes" (§4.2 there), points
  to `∃`, which users destructure. If Matt agrees with D3160's "spelling"
  rule, a Sonnet lane restates the `List.Any` elims as `∃` and deletes
  `memMapAny`. That changes statements and the proofs that use them, so it
  isn't a DeepSeek rename. It goes on the backlog, not in the lanes below.

## 8. Lanes

They don't clash with N1 to N5, S1 or O1 if run in the order given. Every
lane renames with no alias, everywhere the proposal's §5 lists, leaves
records (`docs/proposals/`, `docs/reviews/`, `docs/research/`,
`aoc/NOTES-*.md`) alone, and runs §5's tests:
- `nix develop -c task snap:hashes`, then
  `nix develop -c task test:one -- hash_stability`;
- `bound_to_the_prelude` when it edits `std/core/` or a definition a native
  is bound to;
- `test:one` for each Rust test file whose embedded source or expected names
  it changed (`grep -rn OLDNAME crates --include='*.rs'`);
- `nix develop -c task audit:touched -- <namespaces and AoC days touched>`,
  run by the orchestrator if DeepSeek can't run it in the foreground.

Each DeepSeek brief also carries CLAUDE.md's three lines.

### L1. Names the elaborator builds terms with (Sonnet, 45 min; after D3160)

> Rename `Nat.lessLe` → `Nat.leOfLt`, `Nat.lessTrans` → `Nat.ltTrans`,
> `Nat.lexSecondLess` → `Nat.lexSecondLt`, `Nat.leqFalseOfLess` →
> `Nat.leqFalseOfLt`, `Nat.divTenLess` → `Nat.divTenLt`,
> `Bool.decTrueToBool` → `Bool.toBoolDecTrue`, and `Option.memOfAll` →
> `Option.allSome`. Delete `Nat.modLess` in favour of `Nat.modLt`, writing
> `[ok := h]` where `auto` doesn't find the premise. Move `List.allMem` into
> the core in place of `List.memOfAll` (keep core's argument order), and
> delete `Ring.natAddOne`, moving its uses to `Nat.addOne`
> (`docs/reviews/SW-2195-lemma-names.md` §1, §6). The elaborator names these
> in strings: `core/src/registry.rs:196,213`, `elab/src/derive_induct.rs:25,
> 336,343,344,2365`, `omega.rs:125,642`, `calc.rs:15,369,518`,
> `equations.rs:1082,4527`, `module.rs:2863`. Tests also name them:
> `driver/tests/proofs/function_equations.rs:380`, `function_induct.rs:76`,
> `rt/tests/it/lower.rs:361,407`, `cli/tests/tools/doc.rs:298`,
> `driver/tests/library/search_bench.rs:391`. Update the proving guide's
> three mentions of `Nat.modLess`. Tests: §5, plus `bound_to_the_prelude`,
> `pinned_hashes`, and `test:one` for `function_equations`,
> `function_induct`, `lower`, `doc`, `calc`, the omega tests and the
> `derive_induct` tests. About 160 sites.

Sonnet, not DeepSeek: these are strings that generated kernel terms depend
on (CLAUDE.md: "work near the kernel or proof generation"). D2506 puts std
core changes on Opus. These are renames only, with no change to a statement
or a tactic, so I recommend Sonnet. The orchestrator may choose otherwise.

### L2. `less` → `lt` in `Nat`, `Int`, `Ord` (DeepSeek, 45 min; after L1)

> Apply `docs/reviews/SW-2195-lemma-names.md` §1's rows not marked L1 for
> `Nat`, `Int`, `Ord` and `List.dropConsLess` (`Nat.lessIrrefl` →
> `Nat.ltIrrefl`, `leLessSucc` → `ltSuccOfLe`, `equalOfLess` →
> `equalFalseOfLt`, `lessNotLe` → `leqSuccNotLeq`, `halvesLess` → `halvesLt`,
> `fromDigitsHeadLess` → `fromDigitsLeOfHeadLt`, `headLessArith` →
> `headLtArith`, `Nat`/`Int.lessOfCompare` → `ltOfCompareEqLess`,
> `compareOfLess` → `compareEqLessOfLt`, `Ord.lessLe` → `leOfLt`,
> `lessTrans` → `ltTrans`, `leLessTrans` → `leLtTrans`, `lessLeTrans` →
> `ltLeTrans`, `List.dropConsLess` → `List.lengthDropConsLt`). Also from §2
> and §5: `Nat.toBitsLength` → `Nat.lengthToBits`, `Nat.shiftRightNone` →
> `Nat.shiftRightZero`, and `Nat.xorSome`/`andSome`/`orSome` →
> `xorOfAddPos`/`andOfAddPos`/`orOfAddPos`. Don't rename any name where
> `Less` is the `Ordering` constructor or `less` is a `Bool` function (the
> list under "Staying" in §1). Tests: §5, with `bound_to_the_prelude`
> (`core/Compare.sw`). About 115 sites, 27 of them in AoC.

### L3. Duplicates in `Float`, `Ring`, `Omega`, `Quot` and `Map` (DeepSeek, 40 min; after L2)

> Delete the §6 duplicates not marked L1: the nine `Float.Theory`/`Float`
> copies of `Bool` and `Or` facts, `Float.Theory.notLessSelf`,
> `Ring.lessNotEqual`, `Ring.greaterNotEqual`, `Ring.addNegCancel`,
> `Quot.boolEq` and `Map.orElseNone`, moving each use to the name in the
> "Keep" column. First move `Bool.andFalse` and `Bool.andTrue` from
> `List/SortLemmas.sw:1306,1310` into `Bool/Bool.sw`, and check in
> `crates/elab/src/library.rs` that `Bool/Bool.sw` loads before
> `Float/Theory.sw`; if a kept name isn't visible where a copy is used, stop
> and report. Add `theorem Int.leqRefl (a: Int): Int.leq a a = True` in
> `Int/Int.sw` (Omega's proof), and delete `Omega.intLeqRefl` and
> `Float.Theory.keyRefl`. Rename `Float.Theory.magUnitsLess`, `scaledLess`,
> `halfLess`, `scaleLess` and `quotLess` to `…Lt`, and move
> `Float.Theory.cancelLess` to `Nat.ltOfMulLtMulRight` in `Nat/Arith.sw`.
> All uses are in std. Tests: §5. About 70 sites.

### L4. `List`: conclusion first and the `mem` halves (DeepSeek, 50 min; after N4 and N5)

> Apply the `List` rows of `docs/reviews/SW-2195-lemma-names.md` §2, §4 and
> §5 not marked O1: `sortLength` → `lengthSort`, `permLength` →
> `lengthEqOfPerm`, and the other `…Length` names; `mergeMap`,
> `mergeRunsMap`, `sortWithMap`, `sortByMap` and `sortOnMap` →
> `mapMerge`…`mapSortOn`; `buildRunsJoined`/`Count` →
> `runsJoinedBuildRuns`/`runsCountBuildRuns`; `memTake`, `memDrop`,
> `memDedupAfter`, `memPerm` → `memOf…`; `memOfCountPositive` →
> `memOfCountPos`; `memRemoveFirst` → `memRemoveFirstOther`; `memLeSumBy`
> → `leSumByOfMem`; `getSomeLt` → `ltLengthOfGetSome`; `getOfGetOr` →
> `getEqSomeGetOr`; `getOrMapLt` → `getOrMapOfLt`; `findNoneAll`,
> `findNotNoneAll` and `findAny` → `allOfFindNone`, `allOfFindNotNone` and
> `anyOfFindSome`; `sortedGetOrLe` → `getOrLeOfSorted`; `splitAtFst` →
> `fstSplitAt`. Rename `List.memAppend` → `List.memAppendElim` and add
> `theorem List.memAppend (x: a) (xs: List a) (ys: List a): (x ∈ xs ++ ys)
> ↔ (x ∈ xs ∨ x ∈ ys)` from it and `memAppendLeft`/`Right`; check that each
> old `memAppend` use gets `memAppendElim`. Replace `List.getInRange` with
> `theorem List.isSomeGet (xs: List a) (k: Nat): ((xs.get k).isSome = True)
> ↔ (k < xs.length)`, its two sides swapped, and fix its five uses with
> `.mpr`/`.mp` swapped. Tests: §5. About 170 sites, 72 of them in AoC.

### L5. `Map`, `Set`, `Vec`, `NonEmptyList` (DeepSeek, 40 min; after N1 and N2)

> Apply the `Map`, `Set`, `Vec`, `NonEmptyList`, `Option`, `Float` and
> `Graph` rows of `docs/reviews/SW-2195-lemma-names.md` §2 to §5:
> `Map.containsInsertSame` → `Map.containsInsert`; `Map.containsInsertKeeps`
> and `Set.containsInsertMono` → `…containsInsertOfContains`;
> `Map.getInsertKeeps` → `Map.getInsertOfNotContains`;
> `Graph.containsPushedKeeps` → `Graph.containsPushEdgesOfContains`;
> `Map.memKeysOfContains` → `Map.memKeysIntro`; `Map.getInsertCases` →
> `Map.getInsertEqSomeElim`; `Map.Spec.isLessOf` →
> `Map.Spec.isLessComplete`; `Map.Spec.sameKeyDecide` →
> `Map.Spec.sameKeyBeq`; `Map.containsInEq` → `Map.containsInGetOr`;
> `Map.getIndexByEq` → `Map.getIndexByBeq`; `NonEmptyList.containsMem` →
> `NonEmptyList.containsIff`; `NonEmptyList.toListToNonEmpty` →
> `NonEmptyList.toNonEmptyToList`; `Vec.getToList` → `Vec.getOrToList`;
> `Vec.getOrShiftLeftLt` → `Vec.getOrShiftLeftOfLt`; `Set.popMinNone` →
> `Set.minEqNoneOfPopMinNone` (`minimum…` if N2 has renamed `Set.min`);
> `Nat.decEqFromToBool` → `Nat.toBoolDecEqFrom`; `Option.decSomeToBool` →
> `Option.toBoolDecSome`; `Float.rankIeeeLe`/`Lt` →
> `Float.ieeeLeOfRankLe`/`ieeeLtOfRankLt`. Tests: §5. About 100 sites.

### Added to other lanes

- **O1** (`rangeFrom` start first) also renames `List.memRangeFrom` →
  `List.memRangeFromElim` with a new `↔` `List.memRangeFrom`,
  `memRangeFromOf` → `memRangeFromIntro`, `memRangeBounds` →
  `memRangeElim`, and `memRangeOf` → `memRangeIntro`, along with the strings
  in `omega.rs:492-516`. It also renames the four `sumRange…None` lemmas to
  §5's `sumByRange…EqZero` names. About 80 sites. These statements and that
  code change in O1 anyway, and a separate lane would clash with it.
- **N2** also renames `Vec.ofListToList` → `Vec.fromListCheckedSome` and
  `Vec.ofListDecToList` → `Vec.fromListCheckedDecSome`.
- **N5**'s `List.containsIff` and L5's `NonEmptyList.containsIff` should
  land in the same batch, so the pair stays consistent.

### Order and clashes

L1 → L2 → L3 run one after another: they share `Nat/Arith.sw`, and L3 needs
L2's `Nat.ltIrrefl`. L4 waits for N4 (`List/Distinct.sw`, and
`distinctLength` sits beside N4's lemmas) and N5 (`List/Lemmas.sw`'s `mem*`).
L5 waits for N1 (`getOr`) and N2 (`Set`, `Map`, `Vec`). L4 and L5 can run
side by side, and either can run beside L1 to L3: the files don't overlap.

### Backlog (not lanes yet)

- **G5:** one statement form for `mem…Elim` (`∃`), and delete `memMapAny`
  (Sonnet, about 60 min; it changes statements).
- **The five §7 clarifications** to `docs/proposals/std-naming.md` §1.4, or
  to wherever the naming guide ends up (proving guide, per D3160). A few
  lines; the orchestrator can do it, or add it to L1.
- **The duplicate check** (research T2): `dups2.py` to `dups4.py` found every
  pair in §6 in seconds, so they could be the prototype.

## Calls I made

- Where `less` names the constructor `Less` or a `Bool` function `less`, it
  stays, so 29 names change, not 55. Renaming the `Bool` functions
  (`Int.less`, `Float.less`) is outside this audit.
- `Nat.modLt` is kept over `Nat.modLess`: the `auto` premise is the newer
  form, and the proving guide already teaches it.
- §1 uses rule 6's `Eq` + constant for `compare … = Less`
  (`ltOfCompareEqLess`), and G4's bare constant for `Bool` results
  (`leqFalseOfLt`). That is std's majority.
- `List.allMem` is kept over `List.memOfAll` (more uses, and the right shape
  under rule 5), and moved into the core.
- `Option.allFiniteComplete`, `Pair.allFiniteComplete` and
  `Fin.allComplete` stay, because they name the class field
  `Finite.complete`.
- `filterOfMap` stays, as the documented exception (G2).
- L1 is a Sonnet lane, not Opus (D2506), because it renames strings without
  changing any statement or tactic.
- Parse's `None`/`Some` convention, the `Float.Theory` internals beyond
  `less` and duplicates, and the `Map.Tree`/`Map.Spec` constructor names are
  left for whoever next works in those files.

## D questions

None new. L1 to L3 depend on **D3160** (`lt`, not `less`; open in
`docs/research/std-lemma-libraries.md` §7). If D3160 is no, §1's renames go
the other way (`lt` → `less`, 53 names), and L2 and L3 change with them.

## The 1 November review

`docs/research/rust-codebase-review.md` has no findings about std lemma
names, and `docs/reviews/code-review-std.md`'s naming items (S6, S7, S13) are
the proposal's subject. Nothing to report.
