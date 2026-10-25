-- A lambda whose first parameter hides a function in scope warns
-- (W-LAMBDA-SHADOW): `map xs => …` is a lambda with two parameters, the first
-- named `map`, not a call of `map`. The warning doesn't stop the program from
-- being accepted; renaming the parameter, or bracketing an argument lambda,
-- silences it.
import List (map)
import Std (List)

def shadowed: (Nat -> Nat) -> List Nat -> List Nat := map xs => List.map xs map

def renamed: (Nat -> Nat) -> List Nat -> List Nat := f xs => List.map xs f

def bracketed (xs: List Nat): List Nat := map xs (x => x + 1)

test "the lambdas mean what they say" := shadowed (x => x + 1) [1, 2] == bracketed [1, 2] && renamed (x => x + 1) [1, 2] == [2, 3]
