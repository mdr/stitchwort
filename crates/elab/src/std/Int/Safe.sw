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

-- Two numbers with the same value are equal: their `fits` proofs are too,
-- being proofs that a `Bool` is `True` (`Bool.uniqueEq`).
theorem SafeNat.mkExt (a: Nat) (b: Nat) (p: a <= 9007199254740991) (e: a = b):
    (q: b <= 9007199254740991) -> ({ value = a, fits = p }: SafeNat) = { value = b, fits = q } :=
  J (b' e' => (q': b' <= 9007199254740991) -> ({ value = a, fits = p }: SafeNat) = { value = b', fits = q' })
    (q' => J (r e'' => ({ value = a, fits = p }: SafeNat) = { value = a, fits = r }) rfl
      (Bool.uniqueEq (Nat.leq a 9007199254740991) True p q'))
    e

theorem SafeNat.ext (i: SafeNat) (j: SafeNat) (e: i.value = j.value): i = j :=
  match i, j with
    | { value = a, fits = p }, { value = b, fits = q } => SafeNat.mkExt a b p e q

theorem SafeInt.mkExt (a: Int) (b: Int) (p: Int.natAbs a <= 9007199254740991) (e: a = b):
    (q: Int.natAbs b <= 9007199254740991) -> ({ value = a, fits = p }: SafeInt) = { value = b, fits = q } :=
  J (b' e' => (q': Int.natAbs b' <= 9007199254740991) -> ({ value = a, fits = p }: SafeInt) = { value = b', fits = q' })
    (q' => J (r e'' => ({ value = a, fits = p }: SafeInt) = { value = a, fits = r }) rfl
      (Bool.uniqueEq (Nat.leq (Int.natAbs a) 9007199254740991) True p q'))
    e

theorem SafeInt.ext (i: SafeInt) (j: SafeInt) (e: i.value = j.value): i = j :=
  match i, j with
    | { value = a, fits = p }, { value = b, fits = q } => SafeInt.mkExt a b p e q

-- The number as a `Nat` or `Int`.
def SafeNat.toNat (n: SafeNat): Nat := n.value

def SafeInt.toInt (n: SafeInt): Int := n.value

-- `==` on numbers: equal exactly when their values are.
instance SafeNat.instDecEq: DecEq SafeNat :=
  { decide = i j =>
    if h: i.value = j.value then Yes (SafeNat.ext i j h)
    else No (e => h (Eq.cong (k => k.value) e)) }

instance SafeInt.instDecEq: DecEq SafeInt :=
  { decide = i j =>
    if h: i.value = j.value then Yes (SafeInt.ext i j h)
    else No (e => h (Eq.cong (k => k.value) e)) }

-- In order of their values.
instance SafeNat.instOrd: Ord SafeNat := Ord.byKey (i => i.value) SafeNat.ext

instance SafeInt.instOrd: Ord SafeInt := Ord.byKey (i => i.value) SafeInt.ext

-- The number itself: `"${n}"` is `5`.
instance SafeNat.instShow: Show SafeNat := Show.fromText (i => Nat.toText i.value)

instance SafeInt.instShow: Show SafeInt := Show.fromText (i => Int.toText i.value)
