-- `Int` lemmas proved with `omega` and `ring`: sizes of products, and
-- division and remainders by a divisor that isn't a constant. They live here,
-- not in `Int/Int.sw`, which `omega` itself needs.

-- `|x * y| = |x| * |y|`.
theorem Int.natAbsMul: (x: Int) → (y: Int) → Int.natAbs (x * y) = Int.natAbs x * Int.natAbs y
  | OfNat m, OfNat n => rfl
  | OfNat m, NegSucc n => Int.natAbsNeg (OfNat (m * Succ n))
  | NegSucc m, OfNat n => Int.natAbsNeg (OfNat (Succ m * n))
  | NegSucc m, NegSucc n => rfl

-- Only 0 has size 0.
theorem Int.natAbsZero: (x: Int) → Int.natAbs x = 0 → x = 0
  | OfNat n, h => Eq.cong OfNat h
  | NegSucc n, h => Void.exfalso (Nat.succNotZero n h)

-- The size of `x` as an `Int` is `x` or `-x`.
theorem Int.natAbsCases: (x: Int) → Or (Nat.toInt (Int.natAbs x) = x) (Nat.toInt (Int.natAbs x) = 0 - x)
  | OfNat n => Inl rfl
  | NegSucc n => Inr rfl

-- A number between `-|d|` and `|d|`, exclusive, is smaller in size than
-- `d`.
theorem Int.natAbsLt (x: Int) (d: Int) (low: 0 - Nat.toInt (Int.natAbs d) < x) (high: x < Nat.toInt (Int.natAbs d)):
    Int.natAbs x < Int.natAbs d :=
  match Int.natAbsCases x with
    | Inl same => omega
    | Inr opposite => omega

-- A multiple of `d` smaller in size than `d` is 0 times `d`.
theorem Int.smallMultiple (d: Int) (k: Int) (nonzero: d ≠ 0) (small: Int.natAbs (d * k) < Int.natAbs d): k = 0 :=
  let sizes: Int.natAbs d * Int.natAbs k < Int.natAbs d := rewrite <- Int.natAbsMul d k in small
  let positive: Not (Int.natAbs d = 0) := zero => nonzero (Int.natAbsZero d zero)
  match size: Int.natAbs k with
    | Zero => Int.natAbsZero k size
    | Succ j => Void.exfalso (omega [Nat.leMulPos (Int.natAbs d) (Int.natAbs k) (omega)])

-- Two quotients and remainders of the same number by `d`, each remainder
-- from 0 up to below `|d|`, are the same.
theorem Int.divModUniqueOf (d: Int) (quotient: Int) (remainder: Int) (other: Int) (otherRemainder: Int) (nonzero: d ≠ 0)
    (same: d * quotient + remainder = d * other + otherRemainder) (low: 0 ≤ remainder) (high: remainder < Nat.toInt (Int.natAbs d))
    (otherLow: 0 ≤ otherRemainder) (otherHigh: otherRemainder < Nat.toInt (Int.natAbs d)): And (quotient = other) (remainder = otherRemainder) :=
  let difference: d * (quotient - other) = otherRemainder - remainder := ring [same]
  let small: Int.natAbs (d * (quotient - other)) < Int.natAbs d := rewrite difference in Int.natAbsLt (otherRemainder - remainder) d (omega) (omega)
  let zero: quotient - other = 0 := Int.smallMultiple d (quotient - other) nonzero small
  let none: d * (quotient - other) = 0 := ring [d * zero]
  Both (omega) (omega [difference, none])

-- The quotient and remainder are the only ones with the division law and a
-- remainder from 0 up to below `|d|`.
theorem Int.divModUnique (a: Int) (d: Int) (quotient: Int) (remainder: Int) [auto ok: d ≠ 0] (law: d * quotient + remainder = a)
    (low: 0 ≤ remainder) (high: remainder < Nat.toInt (Int.natAbs d)): And (a / d = quotient) (a % d = remainder) :=
  Int.divModUniqueOf d (a / d) (a % d) quotient remainder ok (Eq.trans (Int.divAddMod a d) (Eq.sym law))
    (Int.modNonneg a d) (Int.modLtAbs a d) low high

-- A nonzero integer has a nonzero size.
theorem Int.natAbsPos (d: Int) (nonzero: d ≠ 0): 0 < Int.natAbs d :=
  let positive: Not (Int.natAbs d = 0) := zero => nonzero (Int.natAbsZero d zero)
  omega

-- `(d * a) / d = a` for a nonzero `d` (Lean's `Int.mul_ediv_cancel_left`).
theorem Int.mulDivCancel (d: Int) (a: Int) [auto ok: d ≠ 0]: (d * a) / d = a :=
  let positive := Int.natAbsPos d ok
  And.left (Int.divModUnique (d * a) d a 0 (ring) (omega) (omega))

-- With `x = d * quotient + remainder`, adding `d * q` adds `q` to the
-- quotient.
theorem Int.addMulRegroup (x: Int) (d: Int) (q: Int) (quotient: Int) (remainder: Int) (law: d * quotient + remainder = x):
    d * (quotient + q) + remainder = x + d * q :=
  ring [law]

-- Adding a multiple of `d`, a negative one too, keeps the remainder (Lean's
-- `Int.add_mul_emod_self_left`).
theorem Int.modAddMul (x: Int) (d: Int) (q: Int) [auto ok: d ≠ 0]: (x + d * q) % d = x % d :=
  And.right (Int.divModUnique (x + d * q) d (x / d + q) (x % d) (Int.addMulRegroup x d q (x / d) (x % d) (Int.divAddMod x d))
    (Int.modNonneg x d) (Int.modLtAbs x d))

-- With `x = d * quotient + remainder`, the remainder plus `y` is `x + y`
-- less `d * quotient`.
theorem Int.remainderAddRegroup (x: Int) (y: Int) (d: Int) (quotient: Int) (remainder: Int) (law: d * quotient + remainder = x):
    remainder + y = (x + y) + d * (0 - quotient) :=
  ring [law]

-- Only the remainder of `x` matters to the remainder of `x + y` (Lean's
-- `Int.emod_add_emod`).
theorem Int.modModAdd (x: Int) (y: Int) (d: Int) [auto ok: d ≠ 0]: (x % d + y) % d = (x + y) % d :=
  rewrite Int.remainderAddRegroup x y d (x / d) (x % d) (Int.divAddMod x d)
  in Int.modAddMul (x + y) d (0 - x / d)

test "Int.mulDivCancel" := (-7 * 13) / -7 == 13 && (5 * -4) / 5 == -4
test "Int.modAddMul" := (3 + -5 * 4) % -5 == 3 % -5 && (-2 + 7 * -3) % 7 == -2 % 7
