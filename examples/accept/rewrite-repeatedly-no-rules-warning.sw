-- expect-warning: W-REWRITE-NO-RULES
-- `len` gives no rules, since every arm is a constructor pattern, but
-- `List.appendNil` does: warn at `len` and continue with the other rules.
import Std (List, Nat)

def len (xs: List Nat): Nat := match xs with
  | [] => 0
  | [_, ..rest] => len rest + 1

theorem a ∀ (xs: List Nat): xs ++ [] = xs := rewrite repeatedly [len, List.appendNil]
