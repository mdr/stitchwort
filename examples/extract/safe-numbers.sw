-- `SafeNat` and `SafeInt` (std/Int/Safe.sw) cross the JS boundary as a
-- `number` instead of a `bigint`: a whole number within 2^53 - 1 of zero,
-- which a JS `number` holds exactly. Decoding refuses a fraction, `NaN`, an
-- infinity, a `bigint` and anything out of range. The result types are
-- bounded too, so encoding is exact: `addSafe` can only return a number it
-- has shown fits.
--
-- run: addSafe { value = 2, fits = rfl } { value = 3, fits = rfl }
-- run: addSafe { value = 9007199254740991, fits = rfl } { value = 1, fits = rfl }
-- run: negateSafe { value = -5, fits = rfl }
-- run: negateSafe { value = 0, fits = rfl }
-- run: negateSafe { value = -9007199254740991, fits = rfl }
-- run: lengths ["ab", "", "cde"]
-- run: bump { count = { value = 41, fits = rfl }, delta = { value = -1, fits = rfl } }
-- run: sumAll [{ value = 1, fits = rfl }, { value = 2, fits = rfl }]
-- run: sameCounter { count = { value = 1, fits = rfl }, delta = { value = -1, fits = rfl } } { count = { value = 1, fits = rfl }, delta = { value = -1, fits = rfl } }
-- run: sameCounter { count = { value = 1, fits = rfl }, delta = { value = -1, fits = rfl } } { count = { value = 2, fits = rfl }, delta = { value = -1, fits = rfl } }
-- run: toSafe 5
-- run: toSafe 9007199254740991
-- run: toSafe 9007199254740992
-- run: toSafeInt (-9007199254740992)
-- run: toSafeInt (-7)

import Std (Int, List, Nat, Option, SafeInt, SafeNat, Text)

-- A bounded sum: `None` when it doesn't fit.
export def addSafe (a: SafeNat) (b: SafeNat): Option SafeNat := SafeNat.ofNat (a.value + b.value)

export def negateSafe (a: SafeInt): Option SafeInt := SafeInt.ofInt (Int.neg a.value)

-- A `Nat` is a `bigint` and a `SafeNat` a `number`, side by side.
export def toSafe (n: Nat): Option SafeNat := SafeNat.ofNat n

export def toSafeInt (n: Int): Option SafeInt := SafeInt.ofInt n

-- Lengths, as numbers a caller can use as array indices.
export def lengths (xs: List Text): List (Option SafeNat) := List.map (x => SafeNat.ofNat (Text.length x)) xs

type Counter = { count: SafeNat, delta: SafeInt }

export def bump (c: Counter): Option SafeNat := SafeNat.ofNat (c.count.value + Int.toNat c.delta.value)

export def sumAll (xs: List SafeNat): Option SafeNat := SafeNat.ofNat (List.foldLeft (acc x => acc + x.value) 0 xs)

-- Records with `SafeNat` and `SafeInt` fields derive `==` (SW-344): equal by value.
export def sameCounter (a: Counter) (b: Counter): Bool := a == b
