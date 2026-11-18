-- A definition whose body has more lambdas than its type shows while its
-- opaque nicknames are hidden: every backend reads its parameters as its
-- body was checked, through the nickname (SW-3933).

import Std.IO (print)

opaque def Fun: Type := Nat -> Nat

opaque def inc: Fun unfolding Fun := m => m + 1

opaque def five: Nat unfolding Fun := inc 4

test "through a nickname" := five == 5

def main (): {IO} () := print (if five == 5 then "five" else "wrong")
