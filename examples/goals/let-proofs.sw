-- A `let` of a proof is shown by its statement only; a `let` of data, with
-- its value.
import Std (List, Eq)

def total (n: Nat): Nat := List.sumBy (List.range n) (r => r)

theorem shifted (n: Nat): total (n + 3) = total (n + 2 + 1) :=
  let wide := n + 3
  let split: wide = n + 2 + 1 := omega
  let both: n + 3 = n + 2 + 1 := Eq.trans split rfl
  let step: (k: Nat) → k + 1 = k + 1 := k => rfl
  ?
