-- Tuple sugar: `(A, B)` is `Pair A B`, `(a, b)` is `MkPair a b`, in types,
-- values and patterns; three or more nest to the right.

def NatText: Type := (Nat, Text)

def triple: (Nat, Bool, Text) := (1, True, "x")

def swap: (a, b) -> (b, a)
  | (x, y) => (y, x)

def third: (a, b, c) -> c
  | (_, _, z) => z

def nested: ((Nat, Nat), Nat) -> Nat
  | ((a, b), c) => a + b + c

-- Tuples inside other patterns.
def firstOf: List (Nat, Nat) -> Nat
  | Nil => 0
  | Cons (a, _) _ => a

-- An inferred type tuple, and an inferred value tuple.
def inferredType: Type := ((Nat, Bool): Type)

def inferredValue: (Nat, Nat) := ((1, 2): (Nat, Nat))

-- Tuples mean the library's `Pair`, whatever a user's own `Pair` is.
def typeIsPair: NatText = Pair Nat Text := rfl

def valueIsMkPair: (1, 2) = MkPair 1 2 := rfl

def nestsToTheRight: (1, 2, 3) = (1, (2, 3)) := rfl

def typeNestsToTheRight: (Nat, Bool, Text) = Pair Nat (Pair Bool Text) := rfl

def swapped: swap (1, 2) = (2, 1) := rfl

def zipped: List.zip [1, 2] [3, 4] = [(1, 3), (2, 4)] := rfl

test "third" := third (1, 2, 3) == 3
test "nested" := nested ((1, 2), 3) == 6
test "firstOf" := firstOf [(5, 6), (7, 8)] == 5
test "grouping" := (1 + 1) == 2
test "dot" := (1, 2).fst == 1
