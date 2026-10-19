-- expect-error: E-AUTO-FALSE
-- `/` needs a proof that the divisor isn't zero, and `0 != 0` is false.
def oops: Nat := 7 / 0
