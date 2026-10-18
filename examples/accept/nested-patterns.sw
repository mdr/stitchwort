-- Patterns can be nested, and numbers can be used as patterns: `2` means
-- `Succ (Succ Zero)`. Equations are tried from top to bottom.

def half : Nat -> Nat
  | 0             => 0
  | 1             => 0
  | Succ (Succ n) => Succ (half n)

-- `Succ n` rebuilds the value the outer `Succ` matched, which is smaller
-- than the argument, so the second recursive call is structural too.
def fib : Nat -> Nat
  | 0             => 0
  | 1             => 1
  | Succ (Succ n) => fib n + fib (Succ n)

def zipSum : List Nat -> List Nat -> List Nat
  | Cons x xs, Cons y ys => Cons (x + y) (zipSum xs ys)
  | _,         _         => Nil

def hasTwo : List a -> Bool
  | Cons _ (Cons _ Nil) => True
  | _                   => False

def describe : Nat -> Nat
  | 3 => 30
  | 7 => 70
  | n => n

-- `a == b` asks the decision procedure for `a = b`, giving a `Bool`.
test "half" := half 101 == 50
test "fib" := fib 20 == 6765
test "zip" := List.length (zipSum [1, 2, 3] [4, 5]) == 2
test "two" := hasTwo [1, 2]
test "not three" := not (hasTwo [1, 2, 3])
test "special" := describe 7 == 70
test "ordinary" := describe 5 == 5
test "booleans" := True == not False

-- Rebuilding a known child keeps it smaller: `Succ n` here is the argument's
-- predecessor, not the argument itself.
def peel : Nat -> Nat
  | 0             => 0
  | 1             => 0
  | Succ (Succ n) => peel (Succ n)

test "peel" := peel 10 == 0
