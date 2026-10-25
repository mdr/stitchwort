-- expect-error: E-PARTIAL-CALLBACK
-- A partial function that passes itself to a helper whose callback row is
-- fixed. (std's `List.map` takes this, see accept/partial-map-self.sw.)
import Std (List, Nat)

def applyAll (f: Nat → {Partial} Nat) (numbers: List Nat): {Partial} (List Nat) :=
  List.map numbers f

def total (n: Nat): {Partial} Nat := List.sum (applyAll total [n])
