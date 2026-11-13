--| The window check is the puzzle's rule: `Window.sumsTo` holds exactly
--| when the number is the sum of two different numbers of the window.

namespace Aoc.Year2020.Day09.Proofs
import Aoc.Year2020.Day09 (..)
import Aoc.Year2020.Day09.Spec (SumOfTwo)
import Std (Bool, DecEq, Decidable, List, Set, Void)

theorem sumsToSound (window: Window) (number: Nat) (sums: window.sumsTo number = True): SumOfTwo window.numbers number :=
  let Witness a (Both member (Both fits (Both differ partner))) := sums
  let partner := (Set.containsFromListIff window.numbers (number - a)).forward partner
  Witness a (Witness (number - a) (Both member (Both partner (Both (same => differ.read.read (omega)) (omega)))))

theorem sumsToComplete (window: Window) (number: Nat) (sum: SumOfTwo window.numbers number): window.sumsTo number = True :=
  let (Witness a (Witness b (Both member (Both partner (Both differ total))))) := sum
  let unequal: ((a + a != number): Bool) = True := DecEq.trueOfNe (same => differ (omega))
  let present: (Set.fromList window.numbers).contains (number - a) = True :=
    (Set.containsFromListIff window.numbers (number - a)).backward (rewrite (omega: number - a = b) in partner)
  Witness a (Both member (Both (omega: a ≤ number) (Both unequal present)))
