-- Numerals as `SafeNat` and `SafeInt` (SW-354): a numeral checked against
-- one is the record with that value, its bound checked by computing it, as
-- for a `Fin` literal, so no proof is written. A negative numeral is a
-- `SafeInt` as it is an `Int`.

import Std (Int, List, Nat, SafeInt, SafeNat)

type Limits = { bytes: SafeNat, offset: SafeInt }

-- Record fields.
def limits: Limits := { bytes = 10, offset = -3 }

-- The bounds themselves, 2^53 - 1 and its negation.
def largest: SafeNat := 9007199254740991

def smallest: SafeInt := -9007199254740991

def zero: SafeInt := -0

-- A list, and a function argument.
def sizes: List SafeNat := [1, 2, 3]

def double (x: SafeNat): Nat := x.value * 2

-- The literal is the record with its value and `rfl`.
theorem tenIs: (10: SafeNat) = { value = 10, fits = rfl } := rfl

theorem minusThreeIs: (-3: SafeInt) = { value = -3, fits = rfl } := rfl

theorem largestValue: largest.value = 9007199254740991 := rfl

theorem zeroValue: zero.value = 0 := rfl

-- Beside a `SafeNat` in a comparison, a numeral is one too.
theorem compared: (limits.bytes == 10 && limits.offset < 0) = True := rfl

-- Numbers that aren't expected as a `SafeNat` are as before.
theorem stillNat: 2 + 3 = 5 := rfl

test "fields" := limits.bytes.value == 10 && limits.offset.value == -3
test "argument" := double 21 == 42
test "list" := sizes.map (x => x.value) == [1, 2, 3]
test "bounds" := smallest.value == -9007199254740991 && largest.value == 9007199254740991
