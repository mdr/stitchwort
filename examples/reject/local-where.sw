-- expect-error: E-WHERE
-- There is no `where` clause: write local definitions in the block.
def sumTo (n: Nat): Nat := go n 0
  where
    go: Nat -> Nat -> Nat
      | Zero, acc => acc
      | Succ k, acc => go k (acc + Succ k)
