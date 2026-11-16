-- Tuple sugar: `(A, B)` is `Pair A B`, `(a, b)` is `MkPair a b`, in types,
-- values and patterns; three or more nest to the right.

import Std (List)

def NatText: Type := (Nat, Text)

def triple: (Nat, Bool, Text) := (1, True, "x")

def swap: (a, b) → (b, a)
  | (x, y) => (y, x)

def third: (a, b, c) → c
  | (_, _, z) => z

def nested: ((Nat, Nat), Nat) → Nat
  | ((a, b), c) => a + b + c

-- Tuples inside other patterns.
def firstOf: List (Nat, Nat) → Nat
  | [] => 0
  | [(a, _), .._] => a

-- An inferred type tuple, and an inferred value tuple.
def inferredType: Type := ((Nat, Bool): Type)

def inferredValue: (Nat, Nat) := ((1, 2): (Nat, Nat))

-- Tuples mean the library's `Pair`, whatever a user's own `Pair` is.
def typeIsPair: NatText = Pair Nat Text := byComputing

def valueIsMkPair: (1, 2) = MkPair 1 2 := byComputing

def nestsToTheRight: (1, 2, 3) = (1, (2, 3)) := byComputing

def typeNestsToTheRight: (Nat, Bool, Text) = Pair Nat (Pair Bool Text) := byComputing

def swapped: swap (1, 2) = (2, 1) := byComputing

def zipped: List.zip [1, 2] [3, 4] = [(1, 3), (2, 4)] := byComputing

test "third" := third (1, 2, 3) == 3
test "nested" := nested ((1, 2), 3) == 6
test "firstOf" := firstOf [(5, 6), (7, 8)] == 5
test "grouping" := (1 + 1) == 2
test "dot" := (1, 2).fst == 1
