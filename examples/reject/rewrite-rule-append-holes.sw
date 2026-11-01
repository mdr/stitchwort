-- expect-error: E-TYPE-MISMATCH
-- A `rewrite` rule's `++` whose operands nothing types waits to be told
-- texts or lists (stage 7), and nothing in the rule tells it: the rule
-- reports that (where main printed the operands' type as `?0 xs`), not
-- only that its left side has no head to look for.
import Std (List, Nat)

theorem appendNothing (xs: List Nat): xs ++ [] = xs :=
  rewrite (rfl: (_ ++ _) = (_ ++ _)) in List.appendNil xs
