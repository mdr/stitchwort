-- Patterns can be nested, and numbers can be used as patterns: `2` means
-- `Succ (Succ Zero)`. Equations are tried from top to bottom.

half : Nat -> Nat
half 0               = 0
half 1               = 0
half (Succ (Succ n)) = Succ (half n)

-- `Succ n` rebuilds the value the outer `Succ` matched, which is smaller
-- than the argument, so the second recursive call is structural too.
fib : Nat -> Nat
fib 0               = 0
fib 1               = 1
fib (Succ (Succ n)) = fib n + fib (Succ n)

zipSum : List Nat -> List Nat -> List Nat
zipSum (Cons x xs) (Cons y ys) = Cons (x + y) (zipSum xs ys)
zipSum _           _           = Nil

hasTwo : List a -> Bool
hasTwo (Cons _ (Cons _ Nil)) = True
hasTwo _                     = False

describe : Nat -> Nat
describe 3 = 30
describe 7 = 70
describe n = n

-- `a == b` asks the decision procedure for `a = b`, giving a `Bool`.
test "half" = half 101 == 50
test "fib" = fib 20 == 6765
test "zip" = length (zipSum [1, 2, 3] [4, 5]) == 2
test "two" = hasTwo [1, 2]
test "not three" = not (hasTwo [1, 2, 3])
test "special" = describe 7 == 70
test "ordinary" = describe 5 == 5
test "booleans" = True == not False

-- Rebuilding a known child keeps it smaller: `Succ n` here is the argument's
-- predecessor, not the argument itself.
peel : Nat -> Nat
peel 0               = 0
peel 1               = 0
peel (Succ (Succ n)) = peel (Succ n)

test "peel" = peel 10 == 0
