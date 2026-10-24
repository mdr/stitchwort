-- expect-error: E-TYPE-MISMATCH
-- A lambda's `[a: Type]` takes an implicit parameter of the type it's
-- checked against, so that type must start with one: here it starts with
-- an explicit `Nat` (docs/proposals/lambda-syntax.md §4.3).

def f: Nat -> Nat := [a: Type] (x: a) => x
