-- expect-error: E-NOT-A-TYPE
-- `->` joins a parameter to a type; a lambda separates its parameter and
-- body with `=>`.
def inc: Nat -> Nat := (x: Nat) -> x + 1
