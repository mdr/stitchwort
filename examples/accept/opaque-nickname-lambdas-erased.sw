-- A parameter before an opaque nickname, and an erased one behind it: the
-- type argument isn't passed at run time, on any backend (SW-3933).

import Std.IO (print)

opaque def Poly: Type 1 := (a: Type) -> Nat

opaque def double (n: Nat): Poly unfolding Poly := a => n + n

opaque def eight: Nat unfolding Poly := double 4 Nat

test "through a nickname" := eight == 8

def main (): {IO} () := print (if eight == 8 then "eight" else "wrong")
