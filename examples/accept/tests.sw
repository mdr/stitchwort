-- `test "name" = expr` checks that a `Bool` is `True`. `stitchwort test` runs
-- them, and caches each result by a hash of everything the test depends on,
-- so a test only runs again after something it uses has changed.

reverse : List a -> List a
reverse Nil         = Nil
reverse (Cons x xs) = append (reverse xs) [x]

equalLists : List Nat -> List Nat -> Bool
equalLists Nil         Nil         = True
equalLists (Cons x xs) (Cons y ys) = if h : x = y then equalLists xs ys else False
equalLists Nil         (Cons y ys) = False
equalLists (Cons x xs) Nil         = False

test "reverse reverses" = equalLists (reverse [1, 2, 3]) [3, 2, 1]
test "reverse twice is the identity" = equalLists (reverse (reverse [1, 2, 3])) [1, 2, 3]
test "division rounds down" = leq (7 / 2) 3
test "remainder" = leq (7 % 2) 1

-- A test is a proof by computation of one fact; a theorem covers every input.
theorem reverseOfSingleton : (x : Nat) -> reverse [x] = [x]
reverseOfSingleton x = rfl
