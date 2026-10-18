-- expect-error: E-TERMINATION
-- A local definition is checked for termination like any other: this one
-- calls itself on an argument that isn't smaller.
def loop (n : Nat) : Nat :=
  def go : Nat -> Nat
    | Zero => 0
    | Succ k => go (Succ k)
  go n
