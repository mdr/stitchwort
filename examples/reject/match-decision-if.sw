-- expect-error: E-TYPE-MISMATCH
-- expect-warning: W-MATCH-DECISION-IF
-- SW-1719 (2021 day 18's `split`): a `match` on a decision replaces the
-- decision where it occurs. An `if` whose branches don't use the proof of its
-- comparison is a test of the `Bool` inside the decision, so it doesn't hold
-- the decision, and the `match` refines nothing. The `No` arm fails with an
-- error about the arm; the warning, given with it, says where the cause is
-- and what to match on instead.
import Std (Nat, Option, Void)

type Number =
  | Regular (value: Nat)
  | Pair (left: Number) (right: Number)

def split: Number → Option Number
  | Regular value => if 10 ≤ value then Some (Pair (Regular (value / 2)) (Regular ((value + 1) / 2))) else None
  | Pair _ _ => None

theorem splitBig (value: Nat) (halves: Number) (some: split (Regular value) = Some halves): 10 ≤ value :=
  match Nat.decLessThan 9 value with
    | Yes big => big
    | No _ => Void.exfalso (Option.noneNotSome halves some)
