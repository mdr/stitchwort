-- expect-error: E-TYPE-MISMATCH
-- expect-warning: W-MATCH-NOT-FOUND
-- SW-1721: an unnamed `match` on an expression the goal doesn't contain
-- refines nothing either, and warns when its arms fail. One whose arms check
-- doesn't warn: unnamed, it is often a case split for the arms' own sake.
import Std (Nat)

def double (n: Nat): Nat := n + n

theorem bad (n: Nat): double n = n + n :=
  match n * 2 with
    | Zero => rfl
    | Succ k => Nat.succNotZero k

theorem splitOnly (n: Nat): double n = n + n :=
  match n * 2 with
    | Zero => rfl
    | Succ k => rfl
