-- expect-error: E-TYPE-MISMATCH
-- `<` on a type without an `Ord` instance.
def earlier (f: Nat -> Nat) (g: Nat -> Nat): Bool := if f < g then True else False
