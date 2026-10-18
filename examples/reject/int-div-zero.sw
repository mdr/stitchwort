-- expect-error: E-AUTO-FALSE
-- `Int.div` needs a proof that the divisor isn't zero, and `0 != 0` is false.
def oops : Int := Int.div (Int.OfNat 7) (Int.OfNat 0)
