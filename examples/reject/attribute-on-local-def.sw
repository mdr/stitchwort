-- expect-error: E-ATTRIBUTE
def sumTo (n: Nat): Nat :=
  @[js.name "loop"] def go (k: Nat): Nat := k
  go n
