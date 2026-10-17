-- Tuple sugar: `(A, B)` is `Pair A B`, `(a, b)` is `MkPair a b`, in types,
-- values and patterns; three or more nest to the right.

NatText : Type
NatText = (Nat, Text)

triple : (Nat, Bool, Text)
triple = (1, True, "x")

swap : (a, b) -> (b, a)
swap (x, y) = (y, x)

third : (a, b, c) -> c
third (_, _, z) = z

nested : ((Nat, Nat), Nat) -> Nat
nested ((a, b), c) = a + b + c

-- Tuples inside other patterns.
firstOf : List (Nat, Nat) -> Nat
firstOf Nil = 0
firstOf (Cons (a, _) _) = a

-- An inferred type tuple, and an inferred value tuple.
inferredType : Type
inferredType = ((Nat, Bool) : Type)

inferredValue : (Nat, Nat)
inferredValue = ((1, 2) : (Nat, Nat))

-- Tuples mean the library's `Pair`, whatever a user's own `Pair` is.
typeIsPair : NatText = Pair Nat Text
typeIsPair = rfl

valueIsMkPair : (1, 2) = MkPair 1 2
valueIsMkPair = rfl

nestsToTheRight : (1, 2, 3) = (1, (2, 3))
nestsToTheRight = rfl

typeNestsToTheRight : (Nat, Bool, Text) = Pair Nat (Pair Bool Text)
typeNestsToTheRight = rfl

swapped : swap (1, 2) = (2, 1)
swapped = rfl

zipped : List.zip [1, 2] [3, 4] = [(1, 3), (2, 4)]
zipped = rfl

test "third" = third (1, 2, 3) == 3
test "nested" = nested ((1, 2), 3) == 6
test "firstOf" = firstOf [(5, 6), (7, 8)] == 5
test "grouping" = (1 + 1) == 2
test "dot" = (1, 2).fst == 1
