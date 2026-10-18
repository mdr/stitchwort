-- expect-error: E-UNKNOWN-FIELD
-- The value on the left fixes `p : Person`, so a mistake inside the lambda is
-- reported as itself, not as a type that can't be inferred.
type Person = { name : Text, age : Nat }

def people : List Person := [{ name = "Ann", age = 30 }]

def names : List Text := people |> List.map (\p => p.nmae)
