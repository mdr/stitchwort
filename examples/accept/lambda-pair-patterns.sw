-- A lambda whose parameter is a tuple or record pattern binds its names to
-- projections instead of being a `match` (SW-319, D550): it is an ordinary
-- lambda, so two copies of it are the same term and a lemma can state it.

import List (foldLeft)
import Std (List)

type Point = { x: Nat, y: Nat }

def weighted (xs: List (Nat, Nat)): Nat := xs.foldLeft 0 (acc (k, v) => acc + k * v)

-- The same lambda written in a different definition.
def weightedAgain (xs: List (Nat, Nat)): Nat := xs.foldLeft 0 (acc (k, v) => acc + k * v)

theorem sameLambda (xs: List (Nat, Nat)): weighted xs = weightedAgain xs := rfl

-- A lemma that mentions the lambda, for an unknown pair.
theorem stepOnPair (acc: Nat) (p: (Nat, Nat)):
    ((a (k, v) => a + k * v): Nat -> (Nat, Nat) -> Nat) acc p = acc + p.fst * p.snd := rfl

-- The lemma applies to a fold step of `weighted`.
theorem weightedNil: weighted [] = 0 := rfl

-- Nested tuples and records.
def nested (xs: List ((Nat, Nat), Nat)): Nat := xs.foldLeft 0 (acc ((a, b), c) => acc + a + b + c)

def pointSum (ps: List Point): Nat := ps.foldLeft 0 (acc { x, y } => acc + x + y)

theorem nestedStep (acc: Nat) (t: ((Nat, Nat), Nat)):
    ((s ((a, b), c) => s + a + b + c): Nat -> ((Nat, Nat), Nat) -> Nat) acc t
      = acc + t.fst.fst + t.fst.snd + t.snd := rfl

-- Two patterns in one lambda.
theorem twoPatterns (p: (Nat, Nat)) (q: (Nat, Nat)):
    (((a, b) (c, d) => a + d): (Nat, Nat) -> (Nat, Nat) -> Nat) p q = p.fst + q.snd := rfl

-- It still computes.
def evaluates: Nat := weighted [(2, 3), (4, 5)]

theorem evaluatesTo: evaluates = 26 := rfl
