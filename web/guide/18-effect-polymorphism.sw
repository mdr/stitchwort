-- A function can leave the effects of its callback open. `{e}` stands for
-- "whatever the callback does": nothing, if it is a pure function.
import Std (Fail, List)
import Std.Fail (fail, toResult)

def applyTwice (f: a -> {e} a) (x: a): {e} a := f (f x)

-- With a pure callback this is a pure function.
test "pure" := applyTwice (n => n + 3) 1 == 7

-- With a callback that may fail, it may fail.
def halve (n: Nat): {Fail} Nat :=
  if n % 2 == 0 then n / 2 else fail "${n} is odd"

test "failing" := toResult (() => applyTwice halve 6) == Err "3 is odd"
test "fine" := toResult (() => applyTwice halve 8) == Ok 2

-- The library works the same way: `mapIn` serves both, and is `map` when
-- the callback is pure.
def squares (xs: List Nat): List Nat := xs.mapIn (n => n * n)
def halves (xs: List Nat): {Fail} (List Nat) := xs.mapIn halve

test "mapIn, pure" := squares [1, 2, 3] == [1, 4, 9]
test "mapIn, failing" := toResult (() => halves [4, 6, 7]) == Err "7 is odd"

-- So a fact about `map` holds for the pure use of `mapIn`.
theorem squaresIsMap (xs: List Nat): squares xs = xs.map (n => n * n) := List.mapInPure _ xs
