-- Day 1 proved, for every list of depths: part 1 counts the measurements
-- deeper than the one before, and part 2, which compares each measurement
-- with the one three places earlier, counts the window sums larger than the
-- one before, as the puzzle adds them up. Part 2 is proved for windows of
-- any size, not just three.

namespace Aoc.Year2021.Day01.Proofs
import Aoc.Year2021.Day01 (..)
import Aoc.Year2021.Day01.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, List, Nat, Void)

-- Counting increases one pair at a time.
theorem increasesCons (a: Nat) (b: Nat) (rest: List Nat):
    increases (Cons a (Cons b rest)) = Bool.toNat (a < b) + increases (Cons b rest) :=
  List.countCons (List.zipWithNext (Cons b rest)) (MkPair a b) (pair => pair.fst < pair.snd)

theorem increasesOverCons (x: Nat) (rest: List Nat) (y: Nat) (ys: List Nat):
    List.count (List.zip (Cons x rest) (Cons y ys)) (pair => pair.fst < pair.snd)
      = Bool.toNat (x < y) + List.count (List.zip rest ys) (pair => pair.fst < pair.snd) :=
  List.countCons (List.zip rest ys) (MkPair x y) (pair => pair.fst < pair.snd)

-- A list zipped with itself one place on is each element paired with the
-- next.
theorem zipNext (x: Nat): (xs: List Nat) → List.zip (Cons x xs) xs = List.zipWithNext (Cons x xs)
  | Nil => rfl
  | Cons y rest => Eq.cong (Cons (MkPair x y)) (zipNext y rest)

-- Part 1 is the puzzle's count, for every list of depths.
theorem part1Correct: (depths: List Nat) → solvePart1 depths = increases depths
  | Nil => rfl
  | Cons x xs => rewrite zipNext x xs in rfl

-- The list from position `m` on starts with the element at `m`, when there
-- is one.
theorem dropAt (d: Nat): (xs: List Nat) → (m: Nat) → m < List.length xs →
    List.drop xs m = Cons (List.getOr xs m d) (List.drop xs (Succ m))
  | Nil, m, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Zero, h => rfl
  | Cons x xs, Succ k, h => dropAt d xs k h

-- And there is none past the end.
theorem dropPast: (xs: List Nat) → (m: Nat) → List.length xs ≤ m → List.drop xs m = Nil
  | Nil, Zero, h => rfl
  | Nil, Succ k, h => rfl
  | Cons x xs, Zero, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x xs, Succ k, h => dropPast xs k h

-- A list with a whole window at its start: the first window, then the
-- windows of the rest.
theorem windowsLong (m: Nat): (xs: List Nat) → m < List.length xs →
    slidingWindows (Succ m) xs = Cons (List.take xs (Succ m)) (slidingWindows (Succ m) (List.drop xs 1))
  | Nil, h => Void.exfalso (Bool.falseNotTrue h)
  | Cons x rest, h =>
    List.filterKeep _ _ _ (rewrite List.lengthTake rest m (omega [h]) in DecEq.refl (Succ m))

-- A list shorter than a window has none.
theorem windowsShort (m: Nat): (xs: List Nat) → List.length xs ≤ m → slidingWindows (Succ m) xs = Nil
  | Nil, h => rfl
  | Cons x rest, h =>
    Eq.trans
      (List.filterSkip (List.map (List.tails rest) (.take (Succ m))) (window => window.length == Succ m) (Cons x (List.take rest m))
        (rewrite List.takeAll rest m (omega [h]) in Decidable.toBoolOfNot _ (same => omega [same, h])))
      (windowsShort m rest (omega [h]))

-- Two windows next to each other share all but their ends, so the later sum
-- is larger exactly when the element it gains is larger than the one it
-- loses.
theorem slideCompare (x: Nat) (shared: Nat) (y: Nat):
    Bool.toNat (x + shared < shared + y) = Bool.toNat (x < y) :=
  cases

-- Part 2, for windows of any size `Succ m`: comparing each measurement with
-- the one `Succ m` places earlier counts the window sums that increase.
theorem windowsCorrect (m: Nat): (depths: List Nat) → increasesOver (Succ m) depths = windowIncreases (Succ m) depths
  | Nil => rfl
  | Cons x rest =>
    match Nat.decLessThan m (List.length rest) with
      | Yes h =>
        -- The window from `x` and the one after it share the `m` elements
        -- after `x`; the later one gains the element at `m` in `rest`.
        let shared := List.sum (List.take rest m)
        let gained := List.getOr rest m 0
        calc increasesOver (Succ m) (Cons x rest)
          _ = List.count (List.zip (Cons x rest) (Cons gained (List.drop rest (Succ m)))) (pair => pair.fst < pair.snd)
            := rewrite dropAt 0 rest m h
          _ = Bool.toNat (x < gained) + increasesOver (Succ m) rest
            := increasesOverCons x rest gained (List.drop rest (Succ m))
          _ = Bool.toNat (x + shared < shared + gained) + windowIncreases (Succ m) rest
            := rewrite slideCompare x shared gained, windowsCorrect m rest
          _ = Bool.toNat (List.sum (List.take (Cons x rest) (Succ m)) < List.sum (List.take rest (Succ m))) + windowIncreases (Succ m) rest
            := rewrite List.sumCons x (List.take rest m), List.takeSucc 0 rest m h, List.sumAppend (List.take rest m) [gained]
          _ = increases (Cons (List.sum (List.take (Cons x rest) (Succ m))) (Cons (List.sum (List.take rest (Succ m))) (List.map (slidingWindows (Succ m) (List.drop rest 1)) List.sum)))
            := rewrite windowsLong m rest h in Eq.sym (increasesCons _ _ _)
          _ = increases (Cons (List.sum (List.take (Cons x rest) (Succ m))) (List.map (slidingWindows (Succ m) rest) List.sum))
            := Eq.cong (ws => increases (Cons (List.sum (List.take (Cons x rest) (Succ m))) (List.map ws List.sum))) (Eq.sym (windowsLong m rest h))
          _ = windowIncreases (Succ m) (Cons x rest)
            := Eq.cong (ws => increases (List.map ws List.sum)) (Eq.sym (windowsLong m (Cons x rest) (omega [h])))
      | No h =>
        calc increasesOver (Succ m) (Cons x rest)
          _ = 0 := rewrite dropPast rest m (omega [h]) in rfl
          _ = windowIncreases (Succ m) (Cons x rest) := atMostOneWindow m x rest (omega [h])

-- A list with at most one window has no increases between windows.
theorem atMostOneWindow (m: Nat) (x: Nat) (rest: List Nat) (short: List.length rest ≤ m): 0 = windowIncreases (Succ m) (Cons x rest) :=
  match Nat.decLessThan m (List.length (Cons x rest)) with
    | Yes one =>
      -- exactly one window
      Eq.sym (calc windowIncreases (Succ m) (Cons x rest)
        _ = increases (List.map (Cons (List.take (Cons x rest) (Succ m)) (slidingWindows (Succ m) rest)) List.sum)
          := Eq.cong (ws => increases (List.map ws List.sum)) (windowsLong m (Cons x rest) one)
        _ = increases [List.sum (List.take (Cons x rest) (Succ m))]
          := Eq.cong (ws => increases (Cons (List.sum (List.take (Cons x rest) (Succ m))) (List.map ws List.sum))) (windowsShort m rest short)
        _ = 0)
    | No none =>
      Eq.sym (Eq.cong (ws => increases (List.map ws List.sum)) (windowsShort m (Cons x rest) (omega [none])))

-- Part 2 is the puzzle's count, for every list of depths.
theorem part2Correct (depths: List Nat): solvePart2 depths = windowIncreases 3 depths := windowsCorrect 2 depths
