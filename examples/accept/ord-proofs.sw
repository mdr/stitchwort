-- Proofs with `Ord`'s laws (docs/proposals/interfaces.md §5.9, §7.6): an
-- instance always comes with them, so generic theorems need no extra
-- "and it's lawful" argument.

import Std (Eq)

-- `List.sort` is sorted, for any ordered type: the `flip` law makes the
-- comparison total, once, for every type (`Ord.leTotal`).
theorem textsSorted (ts: List Text):
    List.Sorted (x y => Ordering.isLessEq (Ord.compare x y)) (List.sort ts) := List.sortSorted ts

-- And a permutation of its input, so it keeps the length.
theorem keepsLength [auto ord: Ord a] (xs: List a): List.length (List.sort xs) = List.length xs := List.sortLength xs

-- For numbers, sorted by `Nat.leq`, as before.
theorem numbersSorted (xs: List Nat): List.Sorted Nat.leq (List.sort xs) := List.sortSortedNat xs

-- Nothing comes before itself.
theorem lessIrreflexive [auto ord: Ord a] (x: a): Not (Ord.compare x x = Less)
  | h => Ordering.equalNotLess (Eq.trans (Eq.sym (Ord.compareSelf x)) h)

-- `Less` is asymmetric: from `flip`.
theorem lessAsymmetric [auto ord: Ord a] (x: a) (y: a) (h: Ord.compare x y = Less): Not (Ord.compare y x = Less)
  | e => Ordering.greaterNotLess (Eq.trans (Eq.sym (Eq.cong Ordering.flip h)) (Eq.trans (Eq.sym (ord.flip x y)) e))

-- The relation agrees with the comparison, by the law that says so.
theorem notBack [auto ord: Ord a] (x: a) (y: a) (h: Ord.lessThan x y): Not (Ord.lessThan y x)
  | back => lessAsymmetric x y (ord.lessThanTo x y h) (ord.lessThanTo y x back)

-- `Ord.max` is one of its arguments.
theorem maxIsOne [auto ord: Ord a] (x: a) (y: a): Or (Ord.max x y = y) (Ord.max x y = x) :=
  match Ord.compare [ord := ord] x y with
    | Less    => Inl rfl
    | Equal   => Inr rfl
    | Greater => Inr rfl

-- Text's laws, which the library proves through `List.compareLex`.
theorem textOrderTransitive (s: Text) (t: Text) (u: Text)
    (h1: Ord.compare s t = Less) (h2: Ord.compare t u = Less): Ord.compare s u = Less := Text.compareTrans s t u h1 h2

theorem appleFirst: Text.compare "apple" "banana" = Less := rfl
