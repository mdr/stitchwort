-- Sums of lists over `Int`: the lemmas that need both `Int/Int.sw` and the
-- `List.sumBy` lemmas of `List/Toolkit.sw`. They live here so that a program
-- using only `Int` does not load the Toolkit (SW-322).

-- The cast of a sum is the sum of the casts.
theorem Int.toIntSumBy (f: a -> Nat): (xs: List a) -> (List.sumBy xs f).toInt = List.sumBy xs (x => (f x).toInt)
  | Nil => rfl
  | Cons x xs =>
    Eq.trans (Eq.cong Nat.toInt (List.sumByCons xs x f))
      (Eq.trans (Eq.cong (t => Int.add (Nat.toInt (f x)) t) (Int.toIntSumBy f xs))
        (Eq.sym (List.sumByCons xs x (y => (f y).toInt))))

-- A common factor comes out of a sum.
theorem Int.sumByMulLeft (c: Int) (f: a -> Int): (xs: List a) -> List.sumBy xs (x => c * f x) = c * List.sumBy xs f
  | Nil => Eq.sym (Int.mulZero c)
  | Cons x xs =>
    Eq.trans (List.sumByCons xs x (y => c * f y))
      (Eq.trans (Eq.cong (t => c * f x + t) (Int.sumByMulLeft c f xs))
        (Eq.sym (Eq.trans (Eq.cong (t => c * t) (List.sumByCons xs x f)) (Int.mulDistribLeft c (f x) (List.sumBy xs f)))))

test "Int.toIntSumBy" := (List.sumBy [1, 2, 3] (x => x * x)).toInt == List.sumBy [1, 2, 3] (x => (x * x).toInt)
