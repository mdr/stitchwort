-- A postponed lambda's parameter keeps a type alias's name when another
-- argument fixes its type (SW-846, the shape of 2024 day 9's
-- `List.mapZipWithScanLeft` proofs). `(n counts => counts.size n)` can't
-- look up `.size` in place, so it waits; `(n counts => Counts.add counts n)`
-- is checked in place and settles `b` by passing `counts` as a `Counts`.
-- `b` is solved with `Counts`, not with the `List Nat` it unfolds to, so
-- the first lambda finds `Counts.size` when it's checked.

import Std (List, Nat)

def Counts: Type := List Nat

def Counts.add (counts: Counts) (n: Nat): Counts := Cons n counts

def Counts.size (counts: Counts) (extra: Nat): Nat := counts.length + extra

def both (f: a → b → Nat) (g: a → b → b) (x: a) (z: b): Nat := f x (g x z)

def sized: Nat := both (n counts => counts.size n) (n counts => Counts.add counts n) 1 [2, 3]

test "the alias's function is found on the postponed parameter" := sized == 4
