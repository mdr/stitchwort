-- expect-error: E-TYPE-MISMATCH
-- expect-warning: W-MATCH-NOT-FOUND
-- SW-2554: a `match` that finds its expression nowhere in the goal leaves
-- the arms the goal as written, so an arm's error and the warning name
-- `sortedKeys xs` rather than printing the body it computes to
-- (`List.mergeRuns …`), as AoC 2020 day 21 met with `list.allergens`. The
-- expression, a proof, is shown as written too.
import Std (List, Nat)

def sortedKeys (xs: List Nat): List Nat := xs.map (x => x + 1) |> .sort

theorem both (xs: List Nat) (nonEmpty: xs ≠ []): xs ≠ [] ∧ xs ≠ [] := Both nonEmpty nonEmpty

theorem keysNonEmpty (xs: List Nat) (nonEmpty: xs ≠ []): (sortedKeys xs).length = xs.length ∧ xs ≠ [] :=
  match both xs nonEmpty with
    | Both first second => first
