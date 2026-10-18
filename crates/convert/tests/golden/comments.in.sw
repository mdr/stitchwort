-- Comments between equations, trailing signature comments, comments in
-- types, and alignment kept or not invented.

-- before f
f : Nat -> Nat  -- trailing on arm form
-- between sig and equations
f Zero = 1
-- before the second equation
f (Succ n) = 2   -- trailing on an equation

g : Nat -> Nat  -- trailing on := form
g n = n

aligned : Nat -> Nat -> Nat
aligned Zero     y = y
aligned (Succ x) y = x

ragged : Nat -> Nat -> Nat
ragged Zero y = y
ragged (Succ x) y = x
