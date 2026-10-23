-- A lambda whose first parameter hides a function in scope warns
-- (W-LAMBDA-SHADOW): `map xs => …` is a lambda with two parameters, the first
-- named `map`, not a call of `map`. The warning doesn't stop the program from
-- being accepted; renaming the parameter, or bracketing an argument lambda,
-- silences it.
import List (map)
import Std (List)

def shadowed: (Nat -> Nat) -> List Nat -> List Nat := map xs => List.map map xs

def renamed: (Nat -> Nat) -> List Nat -> List Nat := f xs => List.map f xs

def bracketed (xs: List Nat): List Nat := map (x => x + 1) xs

test "the lambdas mean what they say" := shadowed (x => x + 1) [1, 2] == bracketed [1, 2] && renamed (x => x + 1) [1, 2] == [2, 3]
