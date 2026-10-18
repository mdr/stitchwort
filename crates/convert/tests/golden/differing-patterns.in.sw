-- Equations with different numbers of patterns must not convert.

f : Nat -> Nat -> Nat
f Zero = \y -> y
f (Succ x) y = x
