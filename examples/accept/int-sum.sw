-- Sums of `Int`s: `List.sumInt`, and `List.sumIntBy` over a function, as
-- `List.sum` and `List.sumBy` are for `Nat`s. The list comes last, so they
-- end a pipeline.

def net (moves: List Int): Int := moves |> List.sumInt

theorem netExample: net [10, -3, -8, 2] = 1 := rfl

theorem emptySum: List.sumInt [] = 0 := rfl

def balance (deltas: List (Text, Int)): Int := deltas |> List.sumIntBy Pair.snd

theorem balanceExample: balance [("a", 5), ("b", -7)] = -2 := rfl

def signedLengths (xs: List (List Nat)): Int :=
  List.sumIntBy (\ys => Int.sub (Nat.toInt (List.length ys)) 1) xs

theorem signedLengthsExample: signedLengths [[1, 2], [], [3]] = 0 := rfl
