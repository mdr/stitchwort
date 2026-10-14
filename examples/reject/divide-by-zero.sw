-- expect-error: E-AUTO-FALSE
-- `/` needs a proof that the divisor isn't zero, and `0 != 0` is false.
oops : Nat
oops = 7 / 0
