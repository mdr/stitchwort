-- `test "name" = expr` checks that a `Bool` is `True`. `stitchwort test` runs
-- them, and caches each result by a hash of everything the test depends on,
-- so a test only runs again after something it uses has changed.

import Std (Nat)

def reverse: List a → List a
  | [] => []
  | [x, ..xs] => (reverse xs).append [x]

def equalLists: List Nat → List Nat → Bool
  | [], [] => True
  | [x, ..xs], [y, ..ys] => if h: x = y then equalLists xs ys else False
  | [], [y, ..ys] => False
  | [x, ..xs], [] => False

test "reverse reverses" := equalLists (reverse [1, 2, 3]) [3, 2, 1]
test "reverse twice is the identity" := equalLists (reverse (reverse [1, 2, 3])) [1, 2, 3]
test "division rounds down" := Nat.leq (7 / 2) 3
test "remainder" := Nat.leq (7 % 2) 1

-- A test is a proof by computation of one fact; a theorem covers every input.
theorem reverseOfSingleton ∀ (x: Nat): reverse [x] = [x] := rfl
