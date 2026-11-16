def f (b: Bool): List Nat := [if b then 1 else 2 -- note
, 3]

def g (b: Bool) (h: Nat -> Nat -> Nat): Nat := h (if b then 1 else 2 -- note
  ) 3
