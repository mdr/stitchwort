-- `if` on a proposition: `if x < y then a else b` means
-- `if _: x < y then a else b`, using the decision procedure `auto` finds.
-- A `Bool` condition is read as a `Bool`, as always.

def smaller (x: Nat) (y: Nat): Nat := if x < y then x else y

test "smaller, first" := smaller 3 5 == 3
test "smaller, second" := smaller 5 3 == 3

def clampTo (hi: Nat) (n: Nat): Nat := if n <= hi then n else hi

test "clamp, below" := clampTo 10 4 == 4
test "clamp, above" := clampTo 10 12 == 10

-- On integers: the comparison's operands decide its type, as for any group.
def sign (n: Int): Int := if n < 0 then -1 else if 0 < n then 1 else 0

test "sign, negative" := sign (-7) == -1
test "sign, zero" := sign 0 == 0
test "sign, positive" := sign 4 == 1

-- `=` and `!=` are propositions too.
def isZero (n: Nat): Bool := if n = 0 then True else False

test "isZero" := isZero 0
test "not isZero" := not (isZero 3)

def nonZero (d: Nat): Nat := if d != 0 then d else 1

test "nonZero" := nonZero 0 == 1

-- `==` is a `Bool`, so this is the ordinary `if`.
def sameList (xs: List Nat) (ys: List Nat): Nat := if xs == ys then 1 else 0

test "sameList, same" := sameList [1, 2] [1, 2] == 1
test "sameList, different" := sameList [1] [2] == 0

-- A `Bool` variable is unchanged.
def pick (b: Bool): Nat := if b then 1 else 2

test "pick" := pick True == 1

-- In a lambda.
def largest (xs: List Nat): Nat := xs.foldLeft 0 (best x => if best < x then x else best)

test "largest" := largest [3, 9, 2] == 9

-- Any result type: here a `Text`.
def describe (n: Nat): Text := if 100 <= n then "big" else "small"

test "describe, big" := describe 150 == "big"
test "describe, small" := describe 3 == "small"
