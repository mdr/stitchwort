-- A bracket that is on one line stays on one line (R8); trailing commas go
-- (D1012); a bracket without commas keeps its closers (D1018, R9).
def a: List Nat := [1, 2, 3]
def b: List Nat := [1, 2]
def c: Person := { name = "Bob", age = 3 }
def d: Nat :=
  Eq.trans (Eq.cong f (g a
      b))
    (h c)
def e: Nat := f (g
  (h x)
  )
