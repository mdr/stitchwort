-- expect-error: E-REFL
-- A cast tested inside another's test makes its own fresh variables: the
-- inner ends `w => w` and `w => z` differ, where `z` is the outer test's
-- fresh variable. An inner test reusing the outer's levels would take `w`
-- for `z` and call them equal.
import Std (Nat, Eq)

def castFn (f g: Nat → Nat) (h: f = g) (n: Nat): Nat := J (y e => Nat) n h

theorem nested ∀
    (hyp: ∀ (z: Nat) => ((w: Nat) => w) = ((w: Nat) => z))
    (h: ((z: Nat) => castFn (w => w) (w => z) (hyp z) 7) = ((z: Nat) => 7)):
    castFn (z => castFn (w => w) (w => z) (hyp z) 7) (z => 7) h 1 = 1 :=
  byComputing
