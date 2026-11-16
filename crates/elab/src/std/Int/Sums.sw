--| Sums of lists over `Int`: the lemmas that need both `Int/Int.sw` and the
--| `List.sumBy` lemmas of `List/Lemmas.sw`.
-- They live here so that a program using only `Int` does not load the list
-- files.

--| The cast of a sum is the sum of the casts.
theorem Int.toIntSumBy ∀ (f: a → Nat) (xs: List a): (List.sumBy xs f).toInt = List.sumBy xs (x => (f x).toInt) :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      calc (List.sumBy [x, ..xs] f).toInt
        _ = (f x + List.sumBy xs f).toInt := Eq.cong Nat.toInt (List.sumByCons xs x f)
        _ = Int.add (Nat.toInt (f x)) (List.sumBy xs (y => (f y).toInt)) :=
          Eq.cong (t => Int.add (Nat.toInt (f x)) t) (Int.toIntSumBy f xs)
        _ = List.sumBy [x, ..xs] (y => (f y).toInt) := Eq.flipped (List.sumByCons xs x (y => (f y).toInt))

--| A common factor comes out of a sum.
theorem Int.sumByMulLeft ∀ (c: Int) (f: a → Int) (xs: List a): List.sumBy xs (x => c * f x) = c * List.sumBy xs f :=
  match xs with
    | [] => (Int.mulZero c).flipped
    | [x, ..xs] =>
      calc List.sumBy [x, ..xs] (y => c * f y)
        _ = c * f x + List.sumBy xs (y => c * f y) := List.sumByCons xs x (y => c * f y)
        _ = c * f x + c * List.sumBy xs f := Eq.cong (t => c * f x + t) (Int.sumByMulLeft c f xs)
        _ = c * (f x + List.sumBy xs f) := Eq.flipped (Int.mulDistribLeft c (f x) (List.sumBy xs f))
        _ = c * List.sumBy [x, ..xs] f := Eq.flipped (Eq.cong (t => c * t) (List.sumByCons xs x f))

test "Int.toIntSumBy" := (List.sumBy [1, 2, 3] (x => x * x)).toInt == List.sumBy [1, 2, 3] (x => (x * x).toInt)
