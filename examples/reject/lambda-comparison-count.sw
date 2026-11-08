-- expect-error: E-AUTO-NONE
def a (xs : List Nat) : Nat := (xs.map (n => 9 < n)).count (b => b)
