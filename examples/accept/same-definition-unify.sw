-- Two stuck calls of one definition with different arguments are equal when
-- their case trees are, and the unifier must see that too, not only `conv`
-- (G6 and G11 in docs/core.md). `ignoresFirst 1 x` and `ignoresFirst 2 x`
-- both compute the predecessor of `x`.

def ignoresFirst (a: Nat) (x: Nat): Nat := match x with
  | Zero => 0
  | Succ m => m

def needSame [a: Nat] (x: Nat) (h: ignoresFirst a x = ignoresFirst 2 x): Nat := a

-- `rfl` is checked against `ignoresFirst 1 x = ignoresFirst 2 x`.
theorem sameAnswer (x: Nat): ignoresFirst 1 x = ignoresFirst 2 x := rfl

-- `a` is given, so the unifier compares the two calls.
def givenA (x: Nat): Nat := needSame [a := 1] x rfl

-- `a` is unsolved until the unifier matches the two calls.
def solvedA (x: Nat): Nat := needSame x rfl

test "the unifier accepts the differing calls" := givenA 5 == 1
test "the unifier solves from the matching call" := solvedA 5 == 2
