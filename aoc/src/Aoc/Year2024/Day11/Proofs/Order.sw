-- "Their order is preserved" doesn't matter to the count: lines with the same
-- stones in another order stay so after every blink (`blinkTimesPerm`), so
-- they end with as many stones (`orderIrrelevant`). This is why counting by
-- number is enough.

namespace Aoc.Year2024.Day11.Proofs
import Aoc.Year2024.Day11 (..)
import Aoc.Year2024.Day11.Spec (..)
import Std (List, Nat)

theorem blinkPerm (stones: List Nat) (others: List Nat) (same: List.Perm stones others): List.Perm (blink stones) (blink others) :=
  List.permFlatMap stones others same change

theorem blinkTimesPerm: (blinks: Nat) → (stones: List Nat) → (others: List Nat) → List.Perm stones others →
    List.Perm (blinkTimes blinks stones) (blinkTimes blinks others)
  | Zero, stones, others, same, p => same p
  | Succ blinks, stones, others, same, p => blinkTimesPerm blinks (blink stones) (blink others) (blinkPerm stones others same) p

-- The same stones in any order end with as many stones, in the puzzle's
-- line and in the program's count.
theorem orderIrrelevant (blinks: Nat) (stones: List Nat) (others: List Nat) (same: List.Perm stones others):
    (blinkTimes blinks stones).length = (blinkTimes blinks others).length :=
  List.permLength (blinkTimes blinks stones) (blinkTimes blinks others) (blinkTimesPerm blinks stones others same)

theorem countOrderIrrelevant (blinks: Nat) (stones: List Nat) (others: List Nat) (same: List.Perm stones others):
    countAfter blinks stones = countAfter blinks others :=
  rewrite countCorrect blinks stones, countCorrect blinks others in orderIrrelevant blinks stones others same
