-- A range at the start of a chain of `|>` steps: the first step finds
-- `List`'s functions from the range, and so do the later ones.
import Std (List, Nat)

def viaRange (n: Nat): List Nat := 0 ..= n |> .flatMap (i => 0 ..= i |> .map (j => i + j)) |> .filter (k => k > 1)

def viaCall (n: Nat): List Nat :=
  List.range 0 (n + 1) |> .flatMap (i => List.range 0 (i + 1) |> .map (j => i + j)) |> .filter (k => k > 1)

def bracketed (n: Nat): List Nat := (0 ..< n) |> .map (i => i * i) |> .filter (k => k > 1)

test "a range starts a chain" := viaRange 3 == viaCall 3
test "the chain's values" := viaRange 2 == [2, 2, 3, 4]
test "a bracketed range" := bracketed 4 == [4, 9]
