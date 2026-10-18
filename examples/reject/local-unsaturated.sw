-- expect-error: E-TERMINATION
-- `go` is in a cycle with its owner, and is used unapplied, so its
-- arguments can't be tracked to show the cycle shrinks.
def map2 (f : Nat -> Nat) : List Nat -> List Nat
  | Nil => Nil
  | Cons x xs => Cons (f x) (map2 f xs)

def owner (xs : List Nat) : List Nat :=
  def go (n : Nat) : Nat := List.length (owner (Cons n Nil))
  map2 go xs
