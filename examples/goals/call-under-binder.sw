-- A call inside a function in the goal stays folded, as one outside does:
-- `n => isSmall n`, not what `isSmall n` computes to.
import Std (Bool, List, Nat)

def isSmall (n: Nat): Bool := n < 10

theorem shown (xs: List Nat): xs.any isSmall = xs.any (n => isSmall n) := ?
