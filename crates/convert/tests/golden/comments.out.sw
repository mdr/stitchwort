-- Comments between equations, trailing signature comments, comments in
-- types, and alignment kept or not invented.

-- before f
def f : Nat -> Nat  -- trailing on arm form
-- between sig and equations
  | Zero => 1
-- before the second equation
  | Succ n => 2   -- trailing on an equation

-- trailing on := form
def g (n : Nat) : Nat := n

def aligned : Nat -> Nat -> Nat
  | Zero,   y => y
  | Succ x, y => x

def ragged : Nat -> Nat -> Nat
  | Zero, y => y
  | Succ x, y => x
