-- A `let`'s name stays in the type of a later `let` that names it:
-- `fact: twice = n + n`, not `n + n = n + n`.
import Std (Nat)

theorem doubled ∀ (n: Nat): n + n = n + n :=
  let twice := n + n
  let fact: twice = n + n := byComputing
  let same: twice = twice := byComputing
  ?
