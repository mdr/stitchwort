--| Each `NonEmptyList` function is its `List` twin on `toList`, and what
--| `NonEmptyList` can say about membership. State facts about a
--| `NonEmptyList` through `toList` and use `List`'s lemmas on them.
-- docs/proposals/non-empty-lists.md §9

import Std (Eq)

--| The basics.

theorem NonEmptyList.toListNotNil ∀ (xs: NonEmptyList a): xs.toList ≠ [] := List.consNotNil xs.head xs.tail

theorem NonEmptyList.lengthToList ∀ (xs: NonEmptyList a): List.length xs.toList = xs.length := byComputing

theorem NonEmptyList.lengthPos ∀ (xs: NonEmptyList a): 0 < xs.length := arithmetic

theorem NonEmptyList.singletonToList ∀ (x: a): (NonEmptyList.singleton x).toList = [x] := byComputing

theorem NonEmptyList.consToList ∀ (x: a) (rest: List a): (NonEmptyList.cons x rest).toList = [x, ..rest] := byComputing

--| The bridges from `List`.

theorem List.toNonEmptyToList ∀ (xs: List a) [auto nonEmpty: xs ≠ []]: (List.toNonEmpty xs).toList = xs := match xs with
  | [] => (nonEmpty byComputing).impossible
  | [x, ..rest] => byComputing

theorem NonEmptyList.toListToNonEmpty ∀ (xs: NonEmptyList a):
    List.toNonEmpty xs.toList [nonEmpty := NonEmptyList.toListNotNil xs] = xs :=
  match xs with | { head = x, tail = rest } => byComputing

theorem List.nonEmptyNil: List.nonEmpty ([]: List a) = None := byComputing

theorem List.nonEmptyCons ∀ (x: a) (rest: List a): List.nonEmpty [x, ..rest] = Some { head = x, tail = rest } :=
  byComputing

theorem NonEmptyList.nonEmptyToList ∀ (xs: NonEmptyList a): List.nonEmpty xs.toList = Some xs := match xs with
  | { head = x, tail = rest } => byComputing

theorem List.nonEmptyToNonEmpty ∀ (xs: List a)
    (h: xs ≠ []):
    List.nonEmpty xs = Some (List.toNonEmpty xs [nonEmpty := h]) :=
  match xs with
    | [] => (h byComputing).impossible
    | [x, ..rest] => byComputing

--| A `NonEmptyList` that `nonEmpty` gives back lists the original list, so a
--| proof can switch to its head and tail without losing the list. This is
--| the converse of [`List.nonEmptyToNonEmpty`], which starts from a list
--| known not to be empty; [`NonEmptyList.nonEmptyToList`] starts from the
--| other side.
theorem List.toListOfNonEmpty ∀ (xs: List a) (ys: NonEmptyList a) (made: List.nonEmpty xs = Some ys): ys.toList = xs :=
  match xs, ys with | [x, ..rest], ordered => rewrite <- Option.someInjective made

--| The `List` twins.

theorem NonEmptyList.countToList ∀ (xs: NonEmptyList a) (p: a → Bool): xs.count p = List.count xs.toList p :=
  byComputing

theorem NonEmptyList.sumByToList ∀ [auto add: Add b] (xs: NonEmptyList a) (f: a → b):
    xs.sumBy f = List.sumBy xs.toList f :=
  byComputing

theorem NonEmptyList.sumToList ∀ [auto add: Add a] (xs: NonEmptyList a): xs.sum = List.sum xs.toList := byComputing

theorem NonEmptyList.productToList ∀ [auto mul: Mul a] (xs: NonEmptyList a): xs.product = List.product xs.toList :=
  byComputing

theorem NonEmptyList.foldLeftToList ∀ (xs: NonEmptyList a) (initial: b) (f: b → a → b):
    xs.foldLeft initial f = List.foldLeft xs.toList initial f :=
  byComputing

theorem NonEmptyList.foldRightToList ∀ (xs: NonEmptyList a) (initial: b) (f: a → b → b):
    xs.foldRight initial f = List.foldRight xs.toList initial f :=
  byComputing

theorem NonEmptyList.reduceSingleton ∀ (x: a) (f: a → a → a): (NonEmptyList.singleton x).reduce f = x := byComputing

theorem NonEmptyList.reduceFoldLeft ∀ (xs: NonEmptyList a) (f: a → a → a):
    xs.reduce f = List.foldLeft xs.tail xs.head f :=
  byComputing

theorem NonEmptyList.lastFromToList ∀ (x: a) (rest: List a):
    List.last [x, ..rest] = Some (NonEmptyList.lastFrom x rest) :=
  match rest with
    | [] => byComputing
    | [y, ..ys] => NonEmptyList.lastFromToList y ys

theorem NonEmptyList.lastToList ∀ (xs: NonEmptyList a): List.last xs.toList = Some xs.last :=
  NonEmptyList.lastFromToList xs.head xs.tail

theorem NonEmptyList.getToList ∀ (xs: NonEmptyList a) (index: Nat): xs.get index = List.get xs.toList index :=
  byComputing

theorem NonEmptyList.getOrToList ∀ (xs: NonEmptyList a) (index: Nat) (fallback: a):
    xs.getOr index fallback = List.getOr xs.toList index fallback :=
  byComputing

theorem NonEmptyList.maximumToList ∀ [auto ord: Ord a] (xs: NonEmptyList a): List.maximum xs.toList = Some xs.maximum :=
  byComputing

theorem NonEmptyList.minimumToList ∀ [auto ord: Ord a] (xs: NonEmptyList a): List.minimum xs.toList = Some xs.minimum :=
  byComputing

theorem NonEmptyList.maxByToList ∀ [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b):
    List.maxBy xs.toList f = Some (xs.maxBy f) :=
  byComputing

theorem NonEmptyList.minByToList ∀ [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b):
    List.minBy xs.toList f = Some (xs.minBy f) :=
  byComputing

theorem NonEmptyList.maximumOfToList ∀ [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b):
    List.maximumOf xs.toList f = Some (xs.maximumOf f) :=
  byComputing

theorem NonEmptyList.minimumOfToList ∀ [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b):
    List.minimumOf xs.toList f = Some (xs.minimumOf f) :=
  byComputing

theorem NonEmptyList.mapToList ∀ (xs: NonEmptyList a) (f: a → b): (xs.map f).toList = List.map xs.toList f :=
  byComputing

theorem NonEmptyList.flatMapToList ∀ (xs: NonEmptyList a) (f: a → List b): xs.flatMap f = List.flatMap xs.toList f :=
  byComputing

theorem NonEmptyList.zipToList ∀ (xs: NonEmptyList a) (ys: NonEmptyList b):
    (xs.zip ys).toList = List.zip xs.toList ys.toList :=
  byComputing

theorem NonEmptyList.zipWithToList ∀ (xs: NonEmptyList a) (ys: NonEmptyList b) (f: a → b → c):
    (xs.zipWith ys f).toList = List.zipWith xs.toList ys.toList f :=
  byComputing

theorem NonEmptyList.reverseOntoToList ∀ (acc: NonEmptyList a) (ys: List a):
    (NonEmptyList.reverseOnto acc ys).toList = List.reverseOnto ys acc.toList :=
  match ys with
    | [] => byComputing
    | [y, ..ys] => NonEmptyList.reverseOntoToList { head = y, tail = [acc.head, ..acc.tail] } ys

theorem NonEmptyList.reverseToList ∀ (xs: NonEmptyList a): xs.reverse.toList = List.reverse xs.toList :=
  NonEmptyList.reverseOntoToList { head = xs.head, tail = [] } xs.tail

theorem NonEmptyList.appendToList ∀ (xs ys: NonEmptyList a): (xs.append ys).toList = List.append xs.toList ys.toList :=
  byComputing

theorem NonEmptyList.appendListToList ∀ (xs: NonEmptyList a) (ys: List a):
    (xs.appendList ys).toList = List.append xs.toList ys :=
  byComputing

theorem NonEmptyList.prependListToList ∀ (prefix: List a) (xs: NonEmptyList a):
    (NonEmptyList.prependList prefix xs).toList = List.append prefix xs.toList :=
  match prefix with | [] | [_, .._] => byComputing

theorem NonEmptyList.sortByToList ∀ (xs: NonEmptyList a) (cmp: a → a → Ordering):
    (xs.sortBy cmp).toList = List.sortBy xs.toList cmp :=
  List.toNonEmptyToList (List.sortBy xs.toList cmp) [nonEmpty := NonEmptyList.sortByNotNil xs cmp]

theorem NonEmptyList.sortToList ∀ [auto ord: Ord a] (xs: NonEmptyList a): xs.sort.toList = List.sort xs.toList :=
  NonEmptyList.sortByToList xs Ord.compare

theorem NonEmptyList.sortSorted ∀ [auto ord: Ord a] (xs: NonEmptyList a):
    List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) xs.sort.toList :=
  J
    (l e => List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) l)
    (List.sortSorted xs.toList)
    (NonEmptyList.sortToList xs).flipped

theorem NonEmptyList.sortPerm ∀ [auto ord: Ord a] (xs: NonEmptyList a): List.Perm xs.sort.toList xs.toList :=
  J (l e => List.Perm l xs.toList) (List.sortPerm xs.toList) (NonEmptyList.sortToList xs).flipped

theorem NonEmptyList.sortLength ∀ [auto ord: Ord a] (xs: NonEmptyList a): xs.sort.length = xs.length :=
  calc xs.sort.length
    _ = xs.sort.toList.length := Eq.flipped (NonEmptyList.lengthToList xs.sort)
    _ = xs.toList.sort.length := Eq.cong (.length) (NonEmptyList.sortToList xs)
    _ = xs.toList.length := List.sortLength xs.toList
    _ = xs.toList.length := NonEmptyList.lengthToList xs

theorem NonEmptyList.containsToList ∀ [auto eq: DecEq a] (xs: NonEmptyList a) (x: a):
    xs.contains x = List.contains xs.toList x :=
  byComputing

theorem NonEmptyList.anyToList ∀ (xs: NonEmptyList a) (p: a → Bool): xs.any p = List.any xs.toList p := byComputing

theorem NonEmptyList.allToList ∀ (xs: NonEmptyList a) (p: a → Bool): xs.all p = List.all xs.toList p := byComputing

theorem NonEmptyList.anyCons ∀ (xs: NonEmptyList a) (p: a → Bool): xs.any p = (p xs.head ∨ List.any xs.tail p) :=
  byComputing

theorem NonEmptyList.allCons ∀ (xs: NonEmptyList a) (p: a → Bool): xs.all p = (p xs.head ∧ List.all xs.tail p) :=
  byComputing

--| Membership.

theorem NonEmptyList.headMem ∀ (xs: NonEmptyList a): NonEmptyList.Mem xs.head xs := Inl byComputing

theorem NonEmptyList.tailMem ∀ (xs: NonEmptyList a) (x: a) (m: x ∈ xs.tail): NonEmptyList.Mem x xs := Inr m

theorem NonEmptyList.lastMem ∀ (xs: NonEmptyList a): NonEmptyList.Mem xs.last xs :=
  List.lastMem xs.toList xs.last (NonEmptyList.lastToList xs)

theorem NonEmptyList.mapMem ∀ (xs: NonEmptyList a) (f: a → b) (x: a)
    (m: NonEmptyList.Mem x xs):
    NonEmptyList.Mem (f x) (xs.map f) :=
  List.memMap xs.toList x m f

theorem NonEmptyList.maximumMem ∀ [auto ord: Ord a] (xs: NonEmptyList a): NonEmptyList.Mem xs.maximum xs :=
  (List.maximumSome xs.toList xs.maximum (NonEmptyList.maximumToList xs)).left

theorem NonEmptyList.maximumLe ∀ [auto ord: Ord a] (xs: NonEmptyList a) (x: a)
    (m: NonEmptyList.Mem x xs):
    x <= xs.maximum :=
  (List.maximumSome xs.toList xs.maximum (NonEmptyList.maximumToList xs)).right x m

theorem NonEmptyList.minimumMem ∀ [auto ord: Ord a] (xs: NonEmptyList a): NonEmptyList.Mem xs.minimum xs :=
  (List.minimumSome xs.toList xs.minimum (NonEmptyList.minimumToList xs)).left

theorem NonEmptyList.minimumLe ∀ [auto ord: Ord a] (xs: NonEmptyList a) (x: a)
    (m: NonEmptyList.Mem x xs):
    xs.minimum <= x :=
  (List.minimumSome xs.toList xs.minimum (NonEmptyList.minimumToList xs)).right x m

theorem NonEmptyList.filterToList ∀ (xs: NonEmptyList a) (p: a → Bool): xs.filter p = List.filter xs.toList p :=
  byComputing

theorem NonEmptyList.filterMapToList ∀ (xs: NonEmptyList a) (f: a → Option b):
    xs.filterMap f = List.filterMap xs.toList f :=
  byComputing

theorem NonEmptyList.takeToList ∀ (xs: NonEmptyList a) (count: Nat): xs.take count = List.take xs.toList count :=
  byComputing

theorem NonEmptyList.dropToList ∀ (xs: NonEmptyList a) (count: Nat): xs.drop count = List.drop xs.toList count :=
  byComputing

theorem NonEmptyList.dedupToList ∀ [auto eq: DecEq a] (xs: NonEmptyList a): xs.dedup.toList = List.dedup xs.toList :=
  byComputing

theorem NonEmptyList.withIndexToList ∀ (xs: NonEmptyList a): xs.withIndex.toList = List.withIndex xs.toList :=
  byComputing

theorem NonEmptyList.mapWithIndexToList ∀ (xs: NonEmptyList a) (f: Nat → a → b):
    (xs.mapWithIndex f).toList = List.mapWithIndex xs.toList f :=
  byComputing

theorem NonEmptyList.findMapToList ∀ (xs: NonEmptyList a) (f: a → Option b): xs.findMap f = List.findMap xs.toList f :=
  byComputing

theorem NonEmptyList.joinToList ∀ (texts: NonEmptyList Text) (separator: Char):
    texts.join separator = Text.join texts.toList separator :=
  byComputing

theorem NonEmptyList.joinWithToList ∀ (texts: NonEmptyList Text) (separator: Text):
    texts.joinWith separator = List.joinWith texts.toList separator :=
  byComputing
