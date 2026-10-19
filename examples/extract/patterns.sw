-- Nested patterns, number patterns and `==`, extracted to JS.
--
-- run: half 101
-- run: fib 20
-- run: hasTwo [1, 2]
-- run: hasTwo [1, 2, 3]
-- run: describe 7
-- run: sameLength [1, 2] [3, 4]
-- run: bigEqual 123456789012345678901234567890

export def half: Nat -> Nat
  | 0             => 0
  | 1             => 0
  | Succ (Succ n) => Succ (half n)

-- Exponential, but random inputs are small.
export def fib: Nat -> Nat
  | 0             => 0
  | 1             => 1
  | Succ (Succ n) => fib n + fib (Succ n)

export def hasTwo: List Nat -> Bool
  | Cons _ (Cons _ Nil) => True
  | _                   => False

export def describe: Nat -> Nat
  | 3 => 30
  | 7 => 70
  | n => n

export def sameLength (xs: List Nat) (ys: List Nat): Bool := List.length xs == List.length ys

export def bigEqual (n: Nat): Bool := n * 2 == n + n
