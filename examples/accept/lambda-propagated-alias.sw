-- A lambda's parameter keeps a type alias's name when its type is settled
-- through another call's result (SW-858, D2092). In `Counts.add (same
-- counts) n`, `same`'s result is checked against `Counts`, which unfolds to
-- `List Nat`; `counts` gets that type, and the name `Counts` is noted for
-- it, so the postponed `(n counts => counts.size n)` still finds
-- `Counts.size`. Only dot notation reads the name: the hidden type
-- arguments stay `List Nat`.

import Std (List, Nat)

def Counts: Type := List Nat

def Counts.add (counts: Counts) (n: Nat): Counts := [n, ..counts]

def Counts.size (counts: Counts) (extra: Nat): Nat := counts.length + extra

def Counts.total (counts: Counts): Nat := counts.sum

def same (x: a): a := x

def both (f: a → b → Nat) (g: a → b → b) (x: a) (z: b): Nat := f x (g x z)

def sized: Nat := both (n counts => counts.size n) (n counts => Counts.add (same counts) n) 1 [2, 3]

def annotated: Nat := both (n (counts: _) => counts.size n) (n counts => Counts.add (same counts) n) 1 [2, 3]

def summed: Nat :=
  both (n counts => counts.total + counts.size n) (n counts => Counts.add (same (same counts)) n) 1 [2, 3]

test "the alias's function is found through a call's result" := sized == 4

test "and on an annotated parameter whose type is left to be found" := annotated == 4

test "and through nested calls" := summed == 10
