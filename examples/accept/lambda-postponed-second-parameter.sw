-- A lambda is checked after the later arguments when any of its parameter
-- types isn't known yet, not only the first (SW-822). Here `n` fixes `f`'s
-- first parameter, so only the second, `b`, waits for `xs`: the lambda
-- `(n acc => n + acc.total)` is still postponed, and `acc.total` works.

import Std (List, Nat)

type Acc = { total: Nat }

def Acc.add (acc: Acc) (n: Nat): Acc := { total = acc.total + n }

def combine (n: Nat) (f: Nat -> b -> c) (xs: List b): List c := List.map xs (x => f n x)
def accs: List Acc := [{ total = 5 }, { total = 7 }]

def sums: List Nat := combine 1 (n acc => n + acc.total) accs

test "the second parameter's type comes from a later argument" := sums == [6, 8]
