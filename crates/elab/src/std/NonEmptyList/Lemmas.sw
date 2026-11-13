--| Each `NonEmptyList` function is its `List` twin on `toList`, and what
--| `NonEmptyList` can say about membership. State facts about a
--| `NonEmptyList` through `toList` and use `List`'s lemmas on them.
-- docs/proposals/non-empty-lists.md §9

import Std (Eq)

--| The basics.

theorem NonEmptyList.toListNotNil ∀ (xs: NonEmptyList a): xs.toList ≠ [] := List.consNotNil xs.head xs.tail

theorem NonEmptyList.lengthToList ∀ (xs: NonEmptyList a): List.length xs.toList = xs.length := rfl

theorem NonEmptyList.lengthPos ∀ (xs: NonEmptyList a): 0 < xs.length := omega

theorem NonEmptyList.singletonToList ∀ (x: a): (NonEmptyList.singleton x).toList = [x] := rfl

theorem NonEmptyList.consToList ∀ (x: a) (rest: List a): (NonEmptyList.cons x rest).toList = [x, ..rest] := rfl

--| The bridges from `List`.

theorem List.toNonEmptyToList ∀ (xs: List a) [auto nonEmpty: xs ≠ []]: (List.toNonEmpty xs).toList = xs :=
  match xs with
    | [] => Void.exfalso (nonEmpty rfl)
    | [x, ..rest] => rfl

theorem NonEmptyList.toListToNonEmpty ∀ (xs: NonEmptyList a): List.toNonEmpty xs.toList [nonEmpty := NonEmptyList.toListNotNil xs] = xs :=
  match xs with
    | { head = x, tail = rest } => rfl

theorem List.nonEmptyNil: List.nonEmpty ([]: List a) = None := rfl

theorem List.nonEmptyCons ∀ (x: a) (rest: List a): List.nonEmpty [x, ..rest] = Some { head = x, tail = rest } := rfl

theorem NonEmptyList.nonEmptyToList ∀ (xs: NonEmptyList a): List.nonEmpty xs.toList = Some xs := match xs with
  | { head = x, tail = rest } => rfl

theorem List.nonEmptyToNonEmpty ∀ (xs: List a) (h: xs ≠ []): List.nonEmpty xs = Some (List.toNonEmpty xs [nonEmpty := h]) :=
  match xs with
    | [] => Void.exfalso (h rfl)
    | [x, ..rest] => rfl

--| A `NonEmptyList` that `nonEmpty` gives back lists the original list, so a
--| proof can switch to its head and tail without losing the list. This is
--| the converse of [`List.nonEmptyToNonEmpty`], which starts from a list
--| known not to be empty; [`NonEmptyList.nonEmptyToList`] starts from the
--| other side.
theorem List.toListOfNonEmpty ∀ (xs: List a) (ys: NonEmptyList a) (made: List.nonEmpty xs = Some ys): ys.toList = xs :=
  match xs, ys with
    | [x, ..rest], ordered => rewrite <- Option.someInjective made in rfl

--| The `List` twins.

theorem NonEmptyList.countToList ∀ (xs: NonEmptyList a) (p: a → Bool): xs.count p = List.count xs.toList p := rfl

theorem NonEmptyList.sumByToList ∀ [auto add: Add b] (xs: NonEmptyList a) (f: a → b): xs.sumBy f = List.sumBy xs.toList f := rfl

theorem NonEmptyList.foldLeftToList ∀ (xs: NonEmptyList a) (initial: b) (f: b → a → b): xs.foldLeft initial f = List.foldLeft xs.toList initial f := rfl

theorem NonEmptyList.foldRightToList ∀ (xs: NonEmptyList a) (initial: b) (f: a → b → b): xs.foldRight initial f = List.foldRight xs.toList initial f := rfl

theorem NonEmptyList.reduceSingleton ∀ (x: a) (f: a → a → a): (NonEmptyList.singleton x).reduce f = x := rfl

theorem NonEmptyList.reduceFoldLeft ∀ (xs: NonEmptyList a) (f: a → a → a): xs.reduce f = List.foldLeft xs.tail xs.head f := rfl

theorem NonEmptyList.lastFromToList ∀ (x: a) (rest: List a): List.last [x, ..rest] = Some (NonEmptyList.lastFrom x rest) :=
  match rest with
    | [] => rfl
    | [y, ..ys] => NonEmptyList.lastFromToList y ys

theorem NonEmptyList.lastToList ∀ (xs: NonEmptyList a): List.last xs.toList = Some xs.last := NonEmptyList.lastFromToList xs.head xs.tail

theorem NonEmptyList.getToList ∀ (xs: NonEmptyList a) (index: Nat): xs.get index = List.get xs.toList index := rfl

theorem NonEmptyList.getOrToList ∀ (xs: NonEmptyList a) (index: Nat) (fallback: a): xs.getOr index fallback = List.getOr xs.toList index fallback := rfl

theorem NonEmptyList.maximumToList ∀ [auto ord: Ord a] (xs: NonEmptyList a): List.maximum xs.toList = Some xs.maximum := rfl

theorem NonEmptyList.minimumToList ∀ [auto ord: Ord a] (xs: NonEmptyList a): List.minimum xs.toList = Some xs.minimum := rfl

theorem NonEmptyList.maxByToList ∀ [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b): List.maxBy xs.toList f = Some (xs.maxBy f) := rfl

theorem NonEmptyList.minByToList ∀ [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b): List.minBy xs.toList f = Some (xs.minBy f) := rfl

theorem NonEmptyList.maximumOfToList ∀ [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b): List.maximumOf xs.toList f = Some (xs.maximumOf f) := rfl

theorem NonEmptyList.minimumOfToList ∀ [auto ord: Ord b] (xs: NonEmptyList a) (f: a → b): List.minimumOf xs.toList f = Some (xs.minimumOf f) := rfl

theorem NonEmptyList.mapToList ∀ (xs: NonEmptyList a) (f: a → b): (xs.map f).toList = List.map xs.toList f := rfl

theorem NonEmptyList.flatMapToList ∀ (xs: NonEmptyList a) (f: a → List b): xs.flatMap f = List.flatMap xs.toList f := rfl

theorem NonEmptyList.zipToList ∀ (xs: NonEmptyList a) (ys: NonEmptyList b): (xs.zip ys).toList = List.zip xs.toList ys.toList := rfl

theorem NonEmptyList.zipWithToList ∀ (xs: NonEmptyList a) (ys: NonEmptyList b) (f: a → b → c): (xs.zipWith ys f).toList = List.zipWith xs.toList ys.toList f := rfl

theorem NonEmptyList.reverseOntoToList ∀ (acc: NonEmptyList a) (ys: List a): (NonEmptyList.reverseOnto acc ys).toList = List.reverseOnto ys acc.toList :=
  match ys with
    | [] => rfl
    | [y, ..ys] => NonEmptyList.reverseOntoToList { head = y, tail = [acc.head, ..acc.tail] } ys

theorem NonEmptyList.reverseToList ∀ (xs: NonEmptyList a): xs.reverse.toList = List.reverse xs.toList :=
  NonEmptyList.reverseOntoToList { head = xs.head, tail = [] } xs.tail

theorem NonEmptyList.appendToList ∀ (xs: NonEmptyList a) (ys: NonEmptyList a): (xs.append ys).toList = List.append xs.toList ys.toList := rfl

theorem NonEmptyList.appendListToList ∀ (xs: NonEmptyList a) (ys: List a): (xs.appendList ys).toList = List.append xs.toList ys := rfl

theorem NonEmptyList.prependListToList ∀ (prefix: List a) (xs: NonEmptyList a): (NonEmptyList.prependList prefix xs).toList = List.append prefix xs.toList :=
  match prefix with
    | [] => rfl
    | [y, ..rest] => rfl

theorem NonEmptyList.sortByToList ∀ (xs: NonEmptyList a) (cmp: a → a → Ordering): (xs.sortBy cmp).toList = List.sortBy xs.toList cmp :=
  List.toNonEmptyToList (List.sortBy xs.toList cmp) [nonEmpty := NonEmptyList.sortByNotNil xs cmp]

theorem NonEmptyList.sortToList ∀ [auto ord: Ord a] (xs: NonEmptyList a): xs.sort.toList = List.sort xs.toList := NonEmptyList.sortByToList xs Ord.compare

theorem NonEmptyList.sortSorted ∀ [auto ord: Ord a] (xs: NonEmptyList a): List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) xs.sort.toList :=
  J (l e => List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) l) (List.sortSorted xs.toList) (Eq.sym (NonEmptyList.sortToList xs))

theorem NonEmptyList.sortPerm ∀ [auto ord: Ord a] (xs: NonEmptyList a): List.Perm xs.sort.toList xs.toList :=
  J (l e => List.Perm l xs.toList) (List.sortPerm xs.toList) (Eq.sym (NonEmptyList.sortToList xs))

theorem NonEmptyList.sortLength ∀ [auto ord: Ord a] (xs: NonEmptyList a): xs.sort.length = xs.length :=
  Eq.trans (Eq.sym (NonEmptyList.lengthToList xs.sort)) (Eq.trans (Eq.cong (.length) (NonEmptyList.sortToList xs)) (Eq.trans (List.sortLength xs.toList) (NonEmptyList.lengthToList xs)))

theorem NonEmptyList.containsToList ∀ [auto eq: DecEq a] (xs: NonEmptyList a) (x: a): xs.contains x = List.contains xs.toList x := rfl

theorem NonEmptyList.anyToList ∀ (xs: NonEmptyList a) (p: a → Bool): xs.any p = List.any xs.toList p := rfl

theorem NonEmptyList.allToList ∀ (xs: NonEmptyList a) (p: a → Bool): xs.all p = List.all xs.toList p := rfl

theorem NonEmptyList.anyCons ∀ (xs: NonEmptyList a) (p: a → Bool): xs.any p = (p xs.head ∨ List.any xs.tail p) := rfl

theorem NonEmptyList.allCons ∀ (xs: NonEmptyList a) (p: a → Bool): xs.all p = (p xs.head ∧ List.all xs.tail p) := rfl

--| Membership.

theorem NonEmptyList.headMem ∀ (xs: NonEmptyList a): NonEmptyList.Mem xs.head xs := Inl rfl

theorem NonEmptyList.tailMem ∀ (xs: NonEmptyList a) (x: a) (m: x ∈ xs.tail): NonEmptyList.Mem x xs := Inr m

theorem NonEmptyList.lastMem ∀ (xs: NonEmptyList a): NonEmptyList.Mem xs.last xs := List.lastMem xs.toList xs.last (NonEmptyList.lastToList xs)

theorem NonEmptyList.mapMem ∀ (xs: NonEmptyList a) (f: a → b) (x: a) (m: NonEmptyList.Mem x xs): NonEmptyList.Mem (f x) (xs.map f) := List.memMap xs.toList x m f

theorem NonEmptyList.maximumMem ∀ [auto ord: Ord a] (xs: NonEmptyList a): NonEmptyList.Mem xs.maximum xs :=
  (List.maximumSome xs.toList xs.maximum (NonEmptyList.maximumToList xs)).left

theorem NonEmptyList.maximumLe ∀ [auto ord: Ord a] (xs: NonEmptyList a) (x: a) (m: NonEmptyList.Mem x xs): x <= xs.maximum :=
  (List.maximumSome xs.toList xs.maximum (NonEmptyList.maximumToList xs)).right x m

theorem NonEmptyList.minimumMem ∀ [auto ord: Ord a] (xs: NonEmptyList a): NonEmptyList.Mem xs.minimum xs :=
  (List.minimumSome xs.toList xs.minimum (NonEmptyList.minimumToList xs)).left

theorem NonEmptyList.minimumLe ∀ [auto ord: Ord a] (xs: NonEmptyList a) (x: a) (m: NonEmptyList.Mem x xs): xs.minimum <= x :=
  (List.minimumSome xs.toList xs.minimum (NonEmptyList.minimumToList xs)).right x m
