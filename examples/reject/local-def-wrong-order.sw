-- expect-error: E-TYPE-MISMATCH
-- A local definition takes the variables it uses in the order they are written
-- (`rest k d`), not the order the compiler splits the arguments in (`d k rest`).

import Std (Nat)

def reach: List Nat -> Nat -> Nat -> Nat -> Bool
  | ls,             c, Zero,   d => c == d
  | Nil,            c, Succ k, d => False
  | Cons line rest, c, Succ k, d =>
    def left: Nat -> Bool
      | Zero   => False
      | Succ b => reach rest b k d
    if Nat.leq line c then left c || reach rest (c + 1) k d else reach rest c k d

theorem leftZero (rest: List Nat) (k: Nat) (d: Nat): reach.left d k rest Zero = False := rfl
