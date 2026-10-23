-- Sums of lists over `Int`: the lemmas that need both `Int/Int.sw` and the
-- `List.sumBy` lemmas of `List/Toolkit.sw`. They live here so that a program
-- using only `Int` does not load the Toolkit (SW-322).

-- The cast of a sum is the sum of the casts.
theorem Int.toIntSumBy (f: a -> Nat): (xs: List a) -> (List.sumBy f xs).toInt = List.sumBy (x => (f x).toInt) xs
  | Nil => rfl
  | Cons x xs =>
    Eq.trans (Eq.cong Nat.toInt (List.sumByCons f x xs))
      (Eq.trans (Eq.cong (t => Int.add (Nat.toInt (f x)) t) (Int.toIntSumBy f xs))
        (Eq.sym (List.sumByCons (y => (f y).toInt) x xs)))

-- A common factor comes out of a sum.
theorem Int.sumByMulLeft (c: Int) (f: a -> Int): (xs: List a) -> List.sumBy (x => c * f x) xs = c * List.sumBy f xs
  | Nil => Eq.sym (Int.mulZero c)
  | Cons x xs =>
    Eq.trans (List.sumByCons (y => c * f y) x xs)
      (Eq.trans (Eq.cong (t => c * f x + t) (Int.sumByMulLeft c f xs))
        (Eq.sym (Eq.trans (Eq.cong (t => c * t) (List.sumByCons f x xs)) (Int.mulDistribLeft c (f x) (List.sumBy f xs)))))

test "Int.toIntSumBy" := (List.sumBy (x => x * x) [1, 2, 3]).toInt == List.sumBy (x => (x * x).toInt) [1, 2, 3]
