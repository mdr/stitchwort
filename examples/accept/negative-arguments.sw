-- A `-` after an operand, with a space before it and none after it, starts a
-- negative argument: `f -2` is `f (-2)` (docs/proposals/negative-arguments.md).
-- A `-` glued to a number is part of the number, so `-1.abs` is `(-1).abs`.
import Std (Float, Int, List, Option)

def shift (n: Int): Int := n + 10
def clamp (x: Int) (lo: Int) (hi: Int): Int := if x < lo then lo else if hi < x then hi else x

test "a literal argument" := shift -2 = 8
test "a name" := (n => shift -n) 3 = 7
def fstOf (p: Pair Int Int): Int := shift -p.fst
test "a field" := fstOf (MkPair 4 5) = 6
test "a later argument" := clamp 1 -2 3 = 1
test "an argument of a lambda body" := [-5, 0, 5].map (x => clamp x -1 1) = [-1, 0, 1]
test "the arguments take one atom each" := shift -2 * 3 = 24
test "the same term as the brackets" := shift -2 = shift (-2)
theorem sameTerm: shift -2 = shift (-2) := rfl

-- Subtraction is as before.
test "tight" := (7: Int) - 1 = 6
test "loose" := (7: Int) - 1 = 6
test "spaced after" := (7: Int) - 1 = 6

-- A negative numeral is one atom.
test "natAbs" := -5.natAbs = 5
test "sub" := -3.sub 5 = -8
test "float floor" := Float.floor -2.5 = -3.0
test "-2.5.floor is (-2.5).floor" := -2.5.floor = -3.0
test "-2.5.abs is (-2.5).abs" := -2.5.abs = 2.5
test "an argument's method" := shift -3.neg = 13

-- Patterns: `Some -1` is `Some (-1)`.
def isMinusOne (o: Option Int): Bool :=
  match o with
    | Some -1 => True
    | _ => False

test "Some -1" := isMinusOne (Some -1) = True
test "not Some -1" := isMinusOne (Some 1) = False
test "None" := isMinusOne None = False
