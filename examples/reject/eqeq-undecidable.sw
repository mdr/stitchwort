-- expect-error: E-AUTO-NONE
-- `==` needs a decision procedure for `=` on the type, and there's none for
-- functions.
inc : Nat -> Nat
inc x = x + 1

same : Bool
same = inc == (\x -> Succ x)
