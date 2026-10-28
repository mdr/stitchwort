-- A result written as a definition that unfolds to a function type takes
-- its argument as one more pattern in each arm.
import Std (Nat)

def Holds (n: Nat): Prop := (m: Nat) → n + m = m + n

theorem holdsAll: (n: Nat) → Holds n
  | n, m => Nat.addComm n m
