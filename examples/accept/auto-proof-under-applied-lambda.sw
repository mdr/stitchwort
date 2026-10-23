-- An `auto` proof inside a lambda that's applied to a term, not a variable
-- (SW-323). In `Eq.cong (t => t + c % 7) h`, the proof that `7 != 0` is an
-- unknown applied to everything in scope, `t` included; once the lambda is
-- applied to `Int.neg x`, matching it against the statement's own proof isn't
-- a plain pattern. The statement `7 != 0` doesn't mention `t`, so the
-- unknown may ignore it, and both sides get the same proof.

import Std (Eq, Int)

theorem congOverMod (c: Int) (x: Int) (z: Int) (h: Int.neg x = z): Int.neg x + c % 7 = z + c % 7 :=
  Eq.cong (t => Int.add t (c % 7)) h

-- The shape SW-314 met: a divisor that's a variable's successor, and the
-- lambda applied to a sum of products.
theorem congOverModSucc (d: Nat) (c: Int) (q: Int) (s: Int):
    (OfNat (Succ d) * q + OfNat (Succ d) * s) + c % OfNat (Succ d) =
      OfNat (Succ d) * (q + s) + c % OfNat (Succ d) :=
  Eq.cong (t => Int.add t (c % OfNat (Succ d))) (Eq.sym (Int.mulDistribLeft (OfNat (Succ d)) q s))
