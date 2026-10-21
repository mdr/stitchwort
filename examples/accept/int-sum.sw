-- Sums of `Int`s: `List.sum`, and `List.sumBy` over a function, are generic
-- (they add with the elements' `Add` instance), so they work on `Int`s as on
-- `Nat`s. The list comes last, so they end a pipeline.

def net (moves: List Int): Int := moves |> List.sum

theorem netExample: net [10, -3, -8, 2] = 1 := rfl

theorem emptySum: List.sum ([]: List Int) = 0 := rfl

def balance (deltas: List (Text, Int)): Int := deltas |> List.sumBy Pair.snd

theorem balanceExample: balance [("a", 5), ("b", -7)] = -2 := rfl

def signedLengths (xs: List (List Nat)): Int :=
  xs.sumBy (ys => Int.sub (Nat.toInt (ys.length)) 1)

theorem signedLengthsExample: signedLengths [[1, 2], [], [3]] = 0 := rfl
