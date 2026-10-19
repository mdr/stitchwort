-- A literal argument of a generic function, before the argument that fixes
-- the type. This used to be rejected: the literal `5` was checked as a `Nat`
-- first, so `a := Nat` and `i: Int` didn't fit. Now the expected result type
-- `Int` is used first (docs/proposals/syntax-conveniences.md, section 7), so
-- `a := Int` before `5` is checked.
def chooseFirst [a: Type] (x: a) (y: a): a := x

def r (i: Int): Int := chooseFirst 5 i

test "chooseFirst 5 i" := r (-3) == 5
