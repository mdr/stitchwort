-- Expected to fail (E-NO-INDUCT): a recursive call inside a `match` under `&&` (§3.1, gap G2).
import Std (Bool, Eq, List, Nat, Option)

def step (owed x: Nat): Option Nat := if x == 0 then None else Some (owed + x)

def stands (owed: Nat) (xs: List Nat): Bool := match xs with
  | [] => owed == 0
  | [x, ..rest] =>
    if x == 1 then
      Nat.leq owed 5
        && (match step owed x with
          | None => False
          | Some still => stands still rest)
    else stands owed rest

theorem t ∀ (owed: Nat) (xs: List Nat) (ok: stands owed xs = True): True := match induct (stands owed xs) with
  | eq1 => ?
