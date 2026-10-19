-- Declarations in any order, and definitions that call each other
-- (docs/proposals/mutual-recursion.md §6.8). Every top-level name is visible
-- throughout the module; definitions that refer to each other are checked
-- together, and their termination is decided for the group.

-- Written top-down: `main` uses what's defined below it.
def main: Nat := total [[1, 2], [3]] + countdown 4

-- Each calls the other on a smaller number.
def isEven: Nat -> Bool
  | 0      => True
  | Succ n => isOdd n

def isOdd: Nat -> Bool
  | 0      => False
  | Succ n => isEven n

-- A wrapper that passes its argument on unchanged, to a helper that makes it
-- smaller: no single call decreases in both, but every way round does.
def countdown (n: Nat): Nat := step n

def step: Nat -> Nat
  | 0      => 0
  | Succ n => countdown n

-- The shape of `size`/`sizeForest` on a tree and a forest, on a list of
-- lists: `total` makes the outer list smaller, `inner` the inner one, and
-- `inner` passes the outer list on unchanged.
def total: List (List Nat) -> Nat
  | Nil         => 0
  | Cons xs xss => inner xs xss

def inner: List Nat -> List (List Nat) -> Nat
  | Nil,       xss => total xss
  | Cons x xs, xss => x + inner xs xss

-- Proofs by mutual induction, about `isEven` and `isOdd`, which are finished
-- before these are checked, so their types compute.
theorem evenNotOdd: (n: Nat) -> isEven n = not (isOdd n)
  | 0      => rfl
  | Succ n => oddNotEven n

theorem oddNotEven: (n: Nat) -> isOdd n = not (isEven n)
  | 0      => rfl
  | Succ n => evenNotOdd n

-- Effectful functions that call each other: after translation, each call is
-- inside a continuation.
ability Counter where
  bump: () -> {Counter} ()

def ping: Nat -> {Counter} ()
  | 0      => ()
  | Succ n =>
    bump()
    pong n

def pong: Nat -> {Counter} ()
  | 0      => ()
  | Succ n => ping n

def countBumps (prog: () -> {Counter} ()): Nat :=
  let run: Nat -> Nat :=
    handle prog() with
      | return x      => \n => n
      | bump u, k     => \n => k() (Succ n)
  run 0

-- A callback passed to a helper as a lambda that calls a member with all
-- its arguments: `\x => stepBy k x` relates `k` to `walk`'s parameter.
def walk: Nat -> Nat
  | 0      => 0
  | Succ k => applyTo (\x => stepBy k x) 1

def stepBy (k: Nat) (x: Nat): Nat := x + walk k

def applyTo (f: Nat -> Nat) (x: Nat): Nat := f x

-- Names stay local: the pattern variable `step` and the lambda's `isOdd` are
-- not the definitions of those names, so they make no dependency on them.
def shadows (step: Nat): Nat := applyTo (\isOdd => isOdd + step) 1

test "main" := main == 6
test "isEven 10" := isEven 10
test "isOdd 7" := isOdd 7
test "total" := total [[1, 2], [], [3, 4]] == 10
test "ping 5 bumps 3 times" := countBumps (\u => ping 5) == 3
test "pong 5 bumps 2 times" := countBumps (\u => pong 5) == 2
test "walk" := walk 3 == 3
test "shadows" := shadows 2 == 3
