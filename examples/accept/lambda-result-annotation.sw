-- A lambda takes no result type, but its body or its `let` can be annotated.

import Std (List, Nat)

def viaBody (xs: List Nat): List Nat :=
  let doubled := (ys: List Nat) => (ys.map (y => y * 2): List Nat)
  doubled xs

def viaLet (xs: List Nat): List Nat :=
  let doubled: List Nat → List Nat := ys => ys.map (y => y * 2)
  doubled xs

test "via body" := viaBody [1, 2] == [2, 4]
test "via let" := viaLet [1, 2] == [2, 4]
