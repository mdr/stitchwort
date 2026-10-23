-- The rest of `Float`'s operations (docs/proposals/float.md §2.5, §4,
-- stage 1b): `* / %`, the rounding functions, the conversions, the total
-- order behind `<` and `<=`, and JavaScript's comparisons by name.
import Std (Float, List, Nat, Option, SafeInt, SafeNat)

-- `*`, `/` and `%` round as IEEE 754 doubles do, and compute in the checker.
-- `/` and `%` need no proof that the divisor isn't zero.
theorem tenths: 0.1 * 3.0 = 0.30000000000000004 := rfl
theorem byZero: 1.0 / 0.0 = Float.infinity := rfl
theorem byMinusZero: 1.0 / -0.0 = -Float.infinity := rfl
theorem zeroByZero: 0.0 / 0.0 = Float.nan := rfl
test "remainder takes the dividend's sign" := -5.5 % 2.0 = -1.5
test "remainder" := 5.5 % 2.0 = 1.5

-- The operand type (D732), with `*`.
def scaled (t: Float): Float := -1 * t
test "-1 * t" := scaled 2.5 = -2.5
def half (t: Float): Float := t / 2
test "a whole literal is exact" := half 5.0 = 2.5

-- `Math.round`: a half goes up, towards +infinity, and a zero keeps its sign.
test "round below a half" := Float.round 0.49999999999999994 = 0.0
test "round minus a half" := Float.round (-0.5) = -0.0
test "round minus zero" := Float.round (-0.0) = -0.0
test "round 2^52 + 1" := Float.round 4503599627370497 = 4503599627370497
test "round a negative tie" := Float.round (-2.5) = -2.0
test "round a tie" := Float.round 2.5 = 3.0
test "floor" := Float.floor (-0.5) = -1.0
test "ceil" := Float.ceil (-0.5) = -0.0
test "trunc" := Float.trunc (-1.5) = -1.0
test "round NaN" := Float.isNaN (Float.round Float.nan) = True

-- Conversions: `ofInt` and `ofNat` round to the nearest double, ties to
-- even; `toInt` is exact, and `None` unless the double is whole.
test "ofInt" := Float.ofInt (-3) = -3.0
test "ofNat ties to even" := Float.ofNat 9007199254740993 = 9007199254740992
test "ofNat beyond the largest" := Float.ofNat (Nat.pow 2 1024) = Float.infinity
test "toInt of minus zero" := Float.toInt (-0.0) = Some 0
test "toInt of a whole number" := Float.toInt (-3.0) = Some (-3)
test "toInt of a fraction" := Float.toInt 0.5 = None
test "toInt of infinity" := Float.toInt Float.infinity = None
test "toInt of 1e100, which isn't 10^100" :=
  Float.toInt 1e100 = Some 10000000000000000159028911097599180468360808563945281389781327557747838772170381060813469985856815104
test "toInt of the largest" := (Float.toInt 1.7976931348623157e308).isSome = True
test "toSafeInt" := Float.toSafeInt 3.0 = SafeInt.ofInt 3
test "toSafeNat of a negative" := Float.toSafeNat (-3.0) = None
test "SafeNat.toFloat" := (SafeNat.ofNat 5 |> Option.map SafeNat.toFloat) = Some 5.0
test "isFinite" := Float.isFinite 1e308 && !(Float.isFinite Float.infinity) && !(Float.isFinite Float.nan)

-- `<` and `<=` are the total order: `-0.0 < 0.0`, the NaN above everything.
theorem zeros: -0.0 < 0.0 := rfl
test "NaN is greatest" := Float.infinity < Float.nan
test "sorted" := List.sort [2.5, Float.nan, -0.0, 0.0, -Float.infinity] = [-Float.infinity, -0.0, 0.0, 2.5, Float.nan]

-- JavaScript's `<` and `<=`, by name: false with a NaN, the zeros equal.
test "ieeeLt zeros" := Float.ieeeLt (-0.0) 0.0 = False
test "ieeeLe zeros" := Float.ieeeLe 0.0 (-0.0) = True
test "ieeeLt NaN" := Float.ieeeLt Float.nan 1.0 = False
test "ieeeLe NaN" := Float.ieeeLe Float.nan Float.nan = False
test "ieeeLt" := Float.ieeeLt (-1.0) 0.5 = True
theorem jsLessIsLessEq (a: Float) (b: Float) (h: Float.ieeeLt a b = True): Float.ieeeLe a b = True :=
  Float.ieeeLtLe a b h

-- `toSource` of the NaN, the infinities and minus zero computes in the
-- checker; the rest go through `toText`, which only the runtimes compute.
test "toSource NaN" := Float.toSource Float.nan = "Float.nan"
test "toSource minus infinity" := Float.toSource (-Float.infinity) = "-Float.infinity"
test "toSource minus zero" := Float.toSource (-0.0) = "-0.0"
