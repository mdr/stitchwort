import Std (Nat, Bool)

def f (a b: Bool): Bool :=
  let y := a || b
  y

def g (a b: Nat): Nat :=
  let y := a + b
  y
