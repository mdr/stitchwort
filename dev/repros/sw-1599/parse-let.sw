import Std (Nat, Bool)

def f (a: Bool) (b: Bool): Bool :=
  let y := a
  || b
  y

def g (a: Nat) (b: Nat): Nat :=
  let y := a
  + b
  y
