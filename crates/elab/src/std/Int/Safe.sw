-- Whole numbers a JavaScript `number` holds exactly (SW-337). At the JS
-- boundary a `SafeNat` or `SafeInt` is a `number`, where a `Nat` or `Int` is
-- a `bigint`: decoding checks that the input is a whole number within the
-- bounds, and the type says the same bounds hold of every value the
-- function returns, so encoding is exact. Inside Stitchwort they are
-- ordinary records, so `n.value` is the `Nat` or `Int`.
--
-- The bounds are 2^53 - 1, the largest integer JS represents exactly (and
-- `Number.MAX_SAFE_INTEGER`), and its negation. The JS runtime's codec
-- checks exactly these bounds, and is used only for these exact
-- declarations (by content hash): change one, and update `SAFE_NAT_HASH` and
-- `SAFE_INT_HASH` in `crates/rt/src/natives.rs` with the codec.

type SafeNat = { value: Nat, fits: value <= 9007199254740991 }

type SafeInt = { value: Int, fits: Int.natAbs value <= 9007199254740991 }

-- `Some` of the number as a `SafeNat`, if it is small enough.
def SafeNat.ofNat (n: Nat): Option SafeNat :=
  if h: n <= 9007199254740991 then Some { value = n, fits = h } else None

-- `Some` of the number as a `SafeInt`, if it is within the bounds.
def SafeInt.ofInt (n: Int): Option SafeInt :=
  if h: Int.natAbs n <= 9007199254740991 then Some { value = n, fits = h } else None
