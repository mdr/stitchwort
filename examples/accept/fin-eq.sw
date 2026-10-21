-- `==` and `<` on `Fin n` values: `Fin` has `DecEq` and `Ord` instances (by
-- number), so positions can be compared.

import Std (Fin)

def isFirst (i: Fin (Succ n)): Bool := i == FZero

def main: Bool :=
  let i: Fin 5 := Fin.ofNat 2
  let j: Fin 5 := Fin.ofNat 4
  i != j && i < j && isFirst (FZero: Fin 3) && isFirst i == False
