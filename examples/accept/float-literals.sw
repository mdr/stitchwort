-- `Float` literals, the operand type of a numeric expression with them, and
-- the arithmetic the checker computes (docs/proposals/float.md §2.3-§2.4,
-- §3.4). Doubles are compared by their bits where the bits are the point.
import Std (Float)

-- A decimal or exponent literal is the nearest double.
test "decimal literal" := (80281.87).bits = 4680253341308362424
test "exponent literal" := (1e3).bits = 4652007308841189376
test "small exponent" := (1.5e-7).bits = 4504762867522569078
test "large exponent" := (2.0E21).bits = 4925560187619831632
test "same double, other spellings" := 0.10 = 1e-1
test "smallest subnormal" := (5e-324).bits = 1
test "zero with a big exponent" := (0e400).bits = 0
test "negative zero with a big exponent" := (-0e-400).bits = 9223372036854775808

-- A whole literal in a `Float` group is that double, exactly.
def big: Float := 9007199254740994
test "2^53 + 2 is a double" := big.bits = 4845873199050653697

-- The operand type (the table in §2.4).
def a: Float := -1 + 0.5
def b: Float := 0.5 + -1
test "-1 + 0.5" := a = -0.5
test "0.5 + -1" := b = -0.5
test "a decimal literal makes the group a Float" := -1 + 0.5 = -0.5

-- `-0` is `-0.0` at `Float` (0x8000000000000000), and `0` elsewhere.
def minusZero: Float := -0
test "minus zero is -0.0" := minusZero.bits = 9223372036854775808
test "minus zero, otherwise an Int" := -0 = (0: Int)
def idInt (n: Int): Int := n
test "a leaf with a literal inside doesn't decide before the minus" := -(idInt 1) = -1

-- A typed operand decides before the minus sign does.
def minus1000 (t: Float): Float := t - 1000
def plusMinusOne (t: Float): Float := t + -1
def minusOnePlus (t: Float): Float := -1 + t
def negated (t: Float): Float := -t
test "t - 1000" := minus1000 80281.87 = 79281.87
test "t + -1" := plusMinusOne 2.5 = 1.5
test "-1 + t" := minusOnePlus 2.5 = 1.5
test "-t" := negated 2.5 = -2.5

-- `+` and `-` round as IEEE 754 doubles do, and compute in the checker.
theorem tenths: 0.1 + 0.2 = 0.30000000000000004 := rfl
theorem halves: 0.5 + 0.25 = 0.75 := rfl
theorem toNegative: 1.0 - 2.0 = -1.0 := rfl
theorem zeros: 0.0 + -0.0 = 0.0 := rfl
theorem negNeg (x: Float): -(-x) = x := Float.negNeg x

-- `==` is the same double (`Object.is`); JS's `===` is `Float.ieeeEq`.
test "zeros differ" := (0.0 == -0.0) = False
test "the NaN equals itself" := (Float.nan == Float.nan) = True
test "ieeeEq zeros" := Float.ieeeEq 0.0 (-0.0) = True
test "ieeeEq NaN" := Float.ieeeEq Float.nan Float.nan = False
test "abs" := Float.abs (-2.5) = 2.5
test "isNaN" := Float.isNaN (Float.infinity - Float.infinity) = True
