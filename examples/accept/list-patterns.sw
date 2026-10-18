-- List patterns: `[]` is `Nil` and `[p, q]` is `Cons p (Cons q Nil)`, the
-- library's constructors by identity.

-- Equations, with a fallback.
describe : List Nat -> Nat
describe [] = 0
describe [x] = x
describe [x, y] = x + y
describe _ = 100

test "describeEmpty" = describe [] == 0
test "describeOne" = describe [7] == 7
test "describeTwo" = describe [3, 4] == 7
test "describeMany" = describe [1, 2, 3] == 100

-- `match`, with an ordinary constructor pattern as the last resort.
firstTwo : List Nat -> Nat
firstTwo xs =
  match xs with
    | [] -> 0
    | [a, b] -> a * b
    | Cons a _ -> a

test "firstTwoPair" = firstTwo [3, 4] == 12
test "firstTwoLonger" = firstTwo [5, 6, 7] == 5

-- A list in a tuple, and a tuple in a list.
pick : (List Nat, List Nat) -> Nat
pick (xs, [y]) = y
pick ([], _) = 1
pick _ = 2

test "pickOne" = pick ([1, 2], [9]) == 9
test "pickEmpty" = pick ([], [1, 2]) == 1
test "pickOther" = pick ([1], [1, 2]) == 2

sumPair : List (Nat, Nat) -> Nat
sumPair [(a, b)] = a + b
sumPair _ = 0

test "sumPairOne" = sumPair [(1, 2)] == 3

-- Nested lists, and a constructor element (no brackets needed).
nested : List (List Nat) -> Nat
nested [[a], [b, c]] = a + b + c
nested _ = 0

test "nestedTwo" = nested [[1], [2, 3]] == 6

justs : List (Maybe Nat) -> Nat
justs [Just a, Nothing] = a
justs _ = 0

test "justsOne" = justs [Just 4, Nothing] == 4

-- `let` and lambda patterns must cover their type, and no list pattern does
-- (see reject/list-pattern-let-refutable.sw), so lists go in `match`.
-- `match` in a lambda body.
lengthOne : List Nat -> Nat
lengthOne = \xs -> match xs with
  | [_] -> 1
  | _ -> 0

test "lengthOneYes" = lengthOne [3] == 1
test "lengthOneNo" = lengthOne [] == 0
