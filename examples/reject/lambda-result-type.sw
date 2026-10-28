-- expect-error: E-PARSE
-- A lambda takes its parameters' types, not a result type: the error points
-- at the `:` before `List Nat`, not at the `let`.

import Std (List, Nat)

def doubledAll (xs: List Nat): List Nat :=
  let doubled := (ys: List Nat): List Nat => ys.map (y => y * 2)
  doubled xs
