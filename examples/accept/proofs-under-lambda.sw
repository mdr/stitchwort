-- `Int.modNat` takes an `auto` proof of `d != 0`. Inside a lambda that is then
-- applied to a variable already in scope, the proof's unknown is applied to
-- that variable twice, which used to fail to unify with the signature's proof
-- (SW-28).

import Std (Int)

theorem congModNat (x: Int) (t: Nat): Int.modNat x (Succ t) = Int.modNat x (Succ t) :=
  Std.Eq.cong (y => Int.modNat y (Succ t)) rfl
