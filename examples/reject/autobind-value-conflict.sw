-- expect-error: E-TYPE-MISMATCH
-- `k` is bound automatically from its uses as an argument of a type, and
-- they need different types: `Nat` for `Box`, `Bool` for `Flag`.
type Box (size : Nat) = { contents : List Nat }
type Flag (on : Bool) = { note : Nat }

def mixed (b : Box k) (f : Flag k) : Nat := 0
