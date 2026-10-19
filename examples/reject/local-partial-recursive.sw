-- expect-error: E-LOCAL-DEFINITION
-- A recursive local definition can't have the `Partial` effect.
def collatz (n: Nat): {Partial} Nat :=
  def go: Nat -> {Partial} Nat
    | Zero => 0
    | Succ k => go (Succ (Succ k))
  go n
