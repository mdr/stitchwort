-- A lambda's parameter whose type was settled through another call's
-- result is shown with the alias it was expected as (SW-858): `counts:
-- Counts`, not `counts: List Nat`.

import Std (List, Nat)

def Counts: Type := List Nat

def Counts.add (counts: Counts) (n: Nat): Counts := [n, ..counts]

def same (x: a): a := x

def both (f: a → b → Nat) (g: a → b → b) (x: a) (z: b): Nat := f x (g x z)

def withGoal: Nat := both (n counts => ?) (n counts => Counts.add (same counts) n) 1 [2, 3]
