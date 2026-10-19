-- Pairs with reject/missing-case.sw.
def isZero: Nat -> Nat
  | Zero   => 1
  | Succ n => 0
