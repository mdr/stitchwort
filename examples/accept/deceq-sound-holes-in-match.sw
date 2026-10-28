-- `DecEq.sound _ _ h` on a branch's hypothesis: the `DecEq` instance is
-- known only once `h`'s type says the comparison is of `Nat`s, and is found
-- then, so the holes needn't be written out.
import Std (DecEq, Nat)

def halfOf (n: Nat) (even: n % 2 = 0): Nat := n / 2

def halfOrZero (n: Nat): Nat :=
  match even: n % 2 == 0 with
    | True =>
      let evenEq := DecEq.sound _ _ even
      halfOf n evenEq
    | False => 0

theorem halfOrZeroFour: halfOrZero 4 = 2 := rfl
