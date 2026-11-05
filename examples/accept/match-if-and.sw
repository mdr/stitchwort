-- SW-1434: a proof follows `if a && b` with one `match e:` on the whole
-- `Bool`, as it follows any other `if`. The `if` is in a function with a
-- `decreasing` measure, whose recursive call is checked after the `if` is
-- written, so it is not yet known then whether the branches use its proof;
-- they don't, and the `if` is on `a && b`.
import Std (Nat, Bool, Void, List, Option)

def run (target: Nat) (front: List Nat) (count: Nat) (sum: Nat) (rest: List Nat): Option (List Nat)
    decreasing front.length + rest.length
:=
  if sum == target && 2 <= count then Some (front.take count)
  else
    match rest with
      | [] => None
      | [next, ..more] => run target front (count + 1) (sum + next) more

theorem runFoundLong (target: Nat) (front: List Nat) (count: Nat) (sum: Nat) (rest: List Nat) (found: List Nat)
    (r: run target front count sum rest = Some found): 2 ≤ count ∨ 0 < rest.length :=
  rewrite run.unfold target front count sum rest at r in
    match e: sum == target && 2 <= count with
      | True => Inl (omega)
      | False =>
        match rest with
          | [] => Void.exfalso (Option.noneNotSome found r)
          | [next, ..more] => Inr (omega)
