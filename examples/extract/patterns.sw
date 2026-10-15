-- Nested patterns, number patterns and `==`, extracted to JS.
--
-- run: half 101
-- run: fib 20
-- run: hasTwo [1, 2]
-- run: hasTwo [1, 2, 3]
-- run: describe 7
-- run: sameLength [1, 2] [3, 4]
-- run: bigEqual 123456789012345678901234567890

export
half : Nat -> Nat
half 0               = 0
half 1               = 0
half (Succ (Succ n)) = Succ (half n)

-- Exponential, but random inputs are small.
export
fib : Nat -> Nat
fib 0               = 0
fib 1               = 1
fib (Succ (Succ n)) = fib n + fib (Succ n)

export
hasTwo : List Nat -> Bool
hasTwo (Cons _ (Cons _ Nil)) = True
hasTwo _                     = False

export
describe : Nat -> Nat
describe 3 = 30
describe 7 = 70
describe n = n

export
sameLength : List Nat -> List Nat -> Bool
sameLength xs ys = length xs == length ys

export
bigEqual : Nat -> Bool
bigEqual n = n * 2 == n + n
