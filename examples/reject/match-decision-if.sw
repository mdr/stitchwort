-- expect-error: E-TYPE-MISMATCH
-- expect-warning: W-MATCH-NOT-FOUND
-- SW-1719 (2021 day 18's `split`): a `match` on a decision replaces the
-- decision where it occurs. An `if` whose branches don't use the proof of its
-- comparison is a test of the decision's `Bool`, so it doesn't hold the
-- decision, and the `match` refines nothing. The `False` arm fails with an
-- error about the arm; the warning, given with it, says the `match` found
-- nothing to replace. Matching on the condition (`Nat.leq 10 value`) refines
-- the `if` (accept/match-decision-if.sw).
import Std (Nat, Option, Void)

type Number =
  | Regular (value: Nat)
  | Pair (left: Number) (right: Number)

def split: Number → Option Number
  | Regular value => if 10 ≤ value then Some (Pair (Regular (value / 2)) (Regular ((value + 1) / 2))) else None
  | Pair _ _ => None

theorem splitBig (value: Nat) (halves: Number) (some: split (Regular value) = Some halves): 10 ≤ value :=
  match Nat.decLessThan 9 value with
    | { holds = True, sound = big, complete = _ } => big rfl
    | { holds = False, sound = _, complete = _ } => Void.exfalso (Option.noneNotSome halves some)
