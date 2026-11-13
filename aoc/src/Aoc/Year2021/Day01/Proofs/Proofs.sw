--| Day 1 proved, for every list of depths: part 1 counts the measurements
--| deeper than the one before, and part 2, which compares each measurement
--| with the one three places earlier, counts the window sums larger than the
--| one before, as the puzzle adds them up. Part 2 is proved for windows of
--| any size, not just three.

namespace Aoc.Year2021.Day01.Proofs
import Aoc.Year2021.Day01 (..)
import Aoc.Year2021.Day01.Spec (..)
import Std (Bool, DecEq, Decidable, Eq, List, Nat, Void)

--| Counting increases one pair at a time.
theorem increasesCons [a: Nat] [b: Nat] [rest: List Nat]:
    increases [a, b, ..rest] = Bool.toNat (a < b) + increases [b, ..rest] :=
  List.countCons (List.zipWithNext [b, ..rest]) (MkPair a b) (pair => pair.fst < pair.snd)

theorem increasesOverCons (x: Nat) (rest: List Nat) (y: Nat) (ys: List Nat):
    List.count (List.zip [x, ..rest] [y, ..ys]) (pair => pair.fst < pair.snd)
      = Bool.toNat (x < y) + (rest.zip ys).count (pair => pair.fst < pair.snd) :=
  List.countCons (List.zip rest ys) (MkPair x y) (pair => pair.fst < pair.snd)

--| A list zipped with itself one place on is each element paired with the
--| next.
theorem zipNext (x: Nat) (xs: List Nat): List.zip [x, ..xs] xs = List.zipWithNext [x, ..xs] := match xs with
  | [] => rfl
  | [y, ..rest] => Eq.cong (Cons (MkPair x y)) (zipNext y rest)

--| Part 1 is the puzzle's count, for every list of depths.
theorem part1Correct (depths: List Nat): solvePart1 depths = increases depths := match depths with
  | [] => rfl
  | [x, ..xs] => rewrite zipNext x xs in rfl

--| A list with a whole window at its start: the first window, then the
--| windows of the rest.
theorem windowsLong (m: Nat) (xs: List Nat) (h: m < xs.length):
    slidingWindows (Succ m) xs = [xs.take (Succ m), ..slidingWindows (Succ m) (xs.drop 1)] := match xs with
      | [x, ..rest] =>
        List.filterKeep _ _ _ (rewrite List.lengthTake rest m (omega [h]) in DecEq.refl (Succ m))

--| A list shorter than a window has none.
theorem windowsShort (m: Nat) (xs: List Nat) (h: xs.length ≤ m): slidingWindows (Succ m) xs = [] := match xs with
  | [] => rfl
  | [x, ..rest] =>
    Eq.trans
      (List.filterSkip _ _ _ (rewrite List.takeAll rest m (omega [h]) in Decidable.toBoolOfNot _ (same => omega [same, h])))
      (windowsShort m rest (omega [h]))

--| Two windows next to each other share all but their ends, so the later sum
--| is larger exactly when the element it gains is larger than the one it
--| loses.
theorem slideCompare (x: Nat) (shared: Nat) (y: Nat):
    Bool.toNat (x + shared < shared + y) = Bool.toNat (x < y) :=
  cases

--| Part 2, for windows of any size `Succ m`: comparing each measurement with
--| the one `Succ m` places earlier counts the window sums that increase.
theorem windowsCorrect (m: Nat) (depths: List Nat): increasesOver (Succ m) depths = windowIncreases (Succ m) depths :=
  match depths with
    | [] => rfl
    | [x, ..rest] =>
      if h: m < List.length rest then
        -- The window from `x` and the one after it share the `m` elements
        -- after `x`; the later one gains the element at `m` in `rest`.
        let shared := List.sum (List.take rest m)
        let gained := List.getOr rest m 0
        calc increasesOver (Succ m) [x, ..rest]
          _ = List.count (List.zip [x, ..rest] [gained, ..List.drop rest (Succ m)]) (pair => pair.fst < pair.snd)
            := rewrite List.dropAt 0 rest m h
          _ = Bool.toNat (x < gained) + increasesOver (Succ m) rest
            := increasesOverCons x rest gained (List.drop rest (Succ m))
          _ = Bool.toNat (x + shared < shared + gained) + windowIncreases (Succ m) rest
            := rewrite slideCompare x shared gained, windowsCorrect m rest
          _ = Bool.toNat (List.sum (List.take [x, ..rest] (Succ m)) < List.sum (List.take rest (Succ m))) + windowIncreases (Succ m) rest
            := rewrite List.sumCons x (List.take rest m), List.takeSucc 0 rest m h, List.sumAppend (List.take rest m) [gained]
          _ = increases [List.sum (List.take [x, ..rest] (Succ m)), List.sum (List.take rest (Succ m)), ..List.map (slidingWindows (Succ m) (List.drop rest 1)) List.sum]
            := rewrite windowsLong m rest h in Eq.sym (increasesCons)
          _ = increases [List.sum (List.take [x, ..rest] (Succ m)), ..List.map (slidingWindows (Succ m) rest) List.sum]
            := Eq.cong (ws => increases [List.sum (List.take [x, ..rest] (Succ m)), ..List.map ws List.sum]) (Eq.sym (windowsLong m rest h))
          _ = windowIncreases (Succ m) [x, ..rest]
            := Eq.cong (ws => increases (List.map ws List.sum)) (Eq.sym (windowsLong m [x, ..rest] (omega [h])))
      else
        calc increasesOver (Succ m) [x, ..rest]
          _ = 0 := rewrite List.dropPast rest m (omega [h]) in rfl
          _ = windowIncreases (Succ m) [x, ..rest] := atMostOneWindow m x rest (omega [h])

--| A list with at most one window has no increases between windows.
theorem atMostOneWindow (m: Nat) (x: Nat) (rest: List Nat) (short: rest.length ≤ m): 0 = windowIncreases (Succ m) [x, ..rest] :=
  if one: m < List.length [x, ..rest] then
    -- exactly one window
    Eq.sym (calc windowIncreases (Succ m) [x, ..rest]
      _ = increases (List.map [List.take [x, ..rest] (Succ m), ..slidingWindows (Succ m) rest] List.sum)
        := Eq.cong (ws => increases (List.map ws List.sum)) (windowsLong m [x, ..rest] one)
      _ = increases [List.sum (List.take [x, ..rest] (Succ m))]
        := Eq.cong (ws => increases [List.sum (List.take [x, ..rest] (Succ m)), ..List.map ws List.sum]) (windowsShort m rest short)
      _ = 0)
  else
    Eq.sym (Eq.cong (ws => increases (List.map ws List.sum)) (windowsShort m [x, ..rest] (omega [one])))

--| Part 2 is the puzzle's count, for every list of depths.
theorem part2Correct (depths: List Nat): solvePart2 depths = windowIncreases 3 depths := windowsCorrect 2 depths
