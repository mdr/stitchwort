-- A test may run partial code (D1183): it's a runtime check, like a unit
-- test in other languages. `stitchwort test` steps it as `stitchwort run`
-- steps a partial `main`; checking never runs it. A test that loops
-- forever is a bug, stopped by whoever ran it.

def collatzSteps: Nat -> {Partial} Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

-- A partial helper that a test calls.
def takes (n: Nat) (steps: Nat): {Partial} Bool := collatzSteps n == steps

-- Mutual recursion, partial.
def isEven: Nat -> {Partial} Bool
  | 0 => True
  | n => isOdd (n - 1)

def isOdd: Nat -> {Partial} Bool
  | 0 => False
  | n => isEven (n - 1)

test "27 takes 111 steps" := collatzSteps 27 == 111
test "1 takes none" := collatzSteps 1 == 0
test "through a partial helper" := takes 97 118
test "in a block" :=
  let steps := collatzSteps 6
  steps == 8 && collatzSteps 7 == 16
test "mutual recursion" := isEven 10 && isOdd 7
test "a total test beside them" := 2 + 2 == 4
