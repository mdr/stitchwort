-- expect-error: E-DUPLICATE
-- Local names are unique within one top-level definition, even when the
-- first is no longer reachable by the time of the second.
def dup (n : Nat) : Nat :=
  def go (k : Nat) : Nat := k
  let x := go n
  def go (k : Nat) : Nat := k + 1
  go x
