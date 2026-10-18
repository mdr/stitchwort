-- A comment inside an equation's left-hand side must not convert.

f : Nat -> Nat -> Nat
f Zero
  -- inside
  y = y
f (Succ x) y = x
