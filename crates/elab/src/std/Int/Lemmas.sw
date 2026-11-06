--| `Int` lemmas proved with `omega` and `ring`: sizes of products, and
--| division and remainders by a divisor that isn't a constant.
-- They live here, not in `Int/Int.sw`, which `omega` itself needs.

--| `|x * y| = |x| * |y|`.
theorem Int.natAbsMul: (x: Int) → (y: Int) → Int.natAbs (x * y) = Int.natAbs x * Int.natAbs y
  | OfNat m, OfNat n => rfl
  | OfNat m, NegSucc n => Int.natAbsNeg (OfNat (m * Succ n))
  | NegSucc m, OfNat n => Int.natAbsNeg (OfNat (Succ m * n))
  | NegSucc m, NegSucc n => rfl

--| Only 0 has size 0.
theorem Int.natAbsZero: (x: Int) → Int.natAbs x = 0 → x = 0
  | OfNat n, h => Eq.cong OfNat h
  | NegSucc n, h => Void.exfalso (Nat.succNotZero n h)

--| The size of `x` as an `Int` is `x` or `-x`.
theorem Int.natAbsCases: (x: Int) → (Nat.toInt (Int.natAbs x) = x) ∨ (Nat.toInt (Int.natAbs x) = 0 - x)
  | OfNat n => Inl rfl
  | NegSucc n => Inr rfl

--| A number between `-|d|` and `|d|`, exclusive, is smaller in size than
--| `d`.
theorem Int.natAbsLt (x: Int) (d: Int) (low: 0 - Nat.toInt (Int.natAbs d) < x) (high: x < Nat.toInt (Int.natAbs d)):
    Int.natAbs x < Int.natAbs d :=
  match Int.natAbsCases x with
    | Inl same => omega
    | Inr opposite => omega

--| A multiple of `d` smaller in size than `d` is 0 times `d`.
theorem Int.smallMultiple (d: Int) (k: Int) (nonzero: d ≠ 0) (small: Int.natAbs (d * k) < Int.natAbs d): k = 0 :=
  let sizes: Int.natAbs d * Int.natAbs k < Int.natAbs d := rewrite <- Int.natAbsMul d k in small
  let positive: Int.natAbs d ≠ 0 := zero => nonzero (Int.natAbsZero d zero)
  match size: Int.natAbs k with
    | Zero => Int.natAbsZero k size
    | Succ j => Void.exfalso (omega [Nat.leMulPos (Int.natAbs d) (Int.natAbs k) (omega)])

--| Two quotients and remainders of the same number by `d`, each remainder
--| from 0 up to below `|d|`, are the same.
theorem Int.divModUniqueOf (d: Int) (quotient: Int) (remainder: Int) (other: Int) (otherRemainder: Int) (nonzero: d ≠ 0)
    (same: d * quotient + remainder = d * other + otherRemainder) (low: 0 ≤ remainder) (high: remainder < Nat.toInt (Int.natAbs d))
    (otherLow: 0 ≤ otherRemainder) (otherHigh: otherRemainder < Nat.toInt (Int.natAbs d)): (quotient = other) ∧ (remainder = otherRemainder) :=
  let difference: d * (quotient - other) = otherRemainder - remainder := ring [same]
  let small: Int.natAbs (d * (quotient - other)) < Int.natAbs d := rewrite difference in Int.natAbsLt (otherRemainder - remainder) d (omega) (omega)
  let zero: quotient - other = 0 := Int.smallMultiple d (quotient - other) nonzero small
  let none: d * (quotient - other) = 0 := ring [d * zero]
  Both (omega) (omega [difference, none])

--| The quotient and remainder are the only ones with the division law and a
--| remainder from 0 up to below `|d|` (so `d` isn't 0).
theorem Int.divModUnique (a: Int) (d: Int) (quotient: Int) (remainder: Int) (law: d * quotient + remainder = a)
    (low: 0 ≤ remainder) (high: remainder < Nat.toInt (Int.natAbs d)): (a / d = quotient) ∧ (a % d = remainder) :=
  let ok: d ≠ 0 := zero => Void.exfalso (omega [rewrite zero at high in high])
  Int.divModUniqueOf d (a / d) (a % d) quotient remainder ok (Eq.trans (Int.divAddMod a d) (Eq.sym law))
    (Int.modNonneg a d) (Int.modLtAbs a d) low high

--| A nonzero integer has a nonzero size.
theorem Int.natAbsPos (d: Int) (nonzero: d ≠ 0): 0 < Int.natAbs d :=
  let positive: Int.natAbs d ≠ 0 := zero => nonzero (Int.natAbsZero d zero)
  omega

--| `(d * a) / d = a` for a nonzero `d` (Lean's `Int.mul_ediv_cancel_left`).
theorem Int.mulDivCancel (d: Int) (a: Int) [auto ok: d ≠ 0]: (d * a) / d = a :=
  let positive := Int.natAbsPos d ok
  And.left (Int.divModUnique (d * a) d a 0 (ring) (omega) (omega))

--| With `x = d * quotient + remainder`, adding `d * q` adds `q` to the
--| quotient.
theorem Int.addMulRegroup (x: Int) (d: Int) (q: Int) (quotient: Int) (remainder: Int) (law: d * quotient + remainder = x):
    d * (quotient + q) + remainder = x + d * q :=
  ring [law]

--| Adding a multiple of `d`, a negative one too, keeps the remainder (Lean's
--| `Int.add_mul_emod_self_left`).
theorem Int.modAddMul (x: Int) (d: Int) (q: Int): (x + d * q) % d = x % d :=
  if zero: d = 0 then rewrite zero, Int.zeroMul q, Int.addZero x in rfl
  else
    And.right (Int.divModUnique (x + d * q) d (x / d + q) (x % d) (Int.addMulRegroup x d q (x / d) (x % d) (Int.divAddMod x d))
      (Int.modNonneg x d) (Int.modLtAbs x d))

--| With `x = d * quotient + remainder`, the remainder plus `y` is `x + y`
--| less `d * quotient`.
theorem Int.remainderAddRegroup (x: Int) (y: Int) (d: Int) (quotient: Int) (remainder: Int) (law: d * quotient + remainder = x):
    remainder + y = (x + y) + d * (0 - quotient) :=
  ring [law]

--| Only the remainder of `x` matters to the remainder of `x + y` (Lean's
--| `Int.emod_add_emod`).
theorem Int.modModAdd (x: Int) (y: Int) (d: Int): (x % d + y) % d = (x + y) % d :=
  rewrite Int.remainderAddRegroup x y d (x / d) (x % d) (Int.divAddMod x d)
  in Int.modAddMul (x + y) d (0 - x / d)

--| `a - b = 0` means `a = b`.
theorem Int.subEqZero (a: Int) (b: Int) (h: a - b = 0): a = b := omega

theorem Int.negOfNatZero (k: Nat) (h: Int.neg (OfNat k) = 0): k = 0 := omega

--| No zero divisors (Lean's `Int.mul_eq_zero`).
theorem Int.mulEqZero: (a: Int) → (b: Int) → a * b = 0 → (a = 0) ∨ (b = 0)
  | OfNat m, OfNat n, h =>
    match Nat.mulEqZero m n (Int.ofNatInjective (m * n) 0 h) with
      | Inl z => Inl (Eq.cong OfNat z)
      | Inr z => Inr (Eq.cong OfNat z)
  | OfNat m, NegSucc n, h =>
    match Nat.mulEqZero m (Succ n) (Int.negOfNatZero (m * Succ n) h) with
      | Inl z => Inl (Eq.cong OfNat z)
      | Inr z => Void.exfalso (omega [z])
  | NegSucc m, OfNat n, h =>
    match Nat.mulEqZero (Succ m) n (Int.negOfNatZero (Succ m * n) h) with
      | Inl z => Void.exfalso (omega [z])
      | Inr z => Inr (Eq.cong OfNat z)
  | NegSucc m, NegSucc n, h =>
    match Nat.mulEqZero (Succ m) (Succ n) (Int.ofNatInjective (Succ m * Succ n) 0 h) with
      | Inl z => Void.exfalso (omega [z])
      | Inr z => Void.exfalso (omega [z])

--| A nonzero factor cancels (Lean's `Int.mul_left_cancel`).
theorem Int.mulCancelLeft (c: Int) (a: Int) (b: Int) (nonzero: c ≠ 0) (h: c * a = c * b): a = b :=
  match Int.mulEqZero c (a - b) (calc c * (a - b)
      _ = c * a - c * b := ring
      _ = c * b - c * b := rewrite h
      _ = 0 := ring) with
    | Inl z => Void.exfalso (nonzero z)
    | Inr z => Int.subEqZero a b z

--| A square is the square of the size.
theorem Int.mulSelf: (x: Int) → x * x = OfNat (Int.natAbs x * Int.natAbs x)
  | OfNat n => rfl
  | NegSucc n => rfl

--| Two squares add up to 0 only when both are 0.
theorem Int.sumSquaresZero (x: Int) (y: Int) (h: x * x + y * y = 0): (x = 0) ∧ (y = 0) :=
  let natural: Int.natAbs x * Int.natAbs x + Int.natAbs y * Int.natAbs y = 0 :=
    Int.ofNatInjective _ 0 (rewrite Int.mulSelf x, Int.mulSelf y at h in h)
  Both (Int.natAbsZero x (Nat.mulSelfZero (Int.natAbs x) (omega))) (Int.natAbsZero y (Nat.mulSelfZero (Int.natAbs y) (omega)))

--| Equal squares: the same number, or its negation.
theorem Int.squaresEq (x: Int) (y: Int) (h: x * x = y * y): (x = y) ∨ (x + y = 0) :=
  match Int.mulEqZero (x - y) (x + y) (ring [h]) with
    | Inl z => Inl (Int.subEqZero x y z)
    | Inr z => Inr z

test "Int.mulEqZero" := (0 * -3 == 0) && (-4 * 5 != 0)
test "Int.mulDivCancel" := (-7 * 13) / -7 == 13 && (5 * -4) / 5 == -4
test "Int.modAddMul" := (3 + -5 * 4) % -5 == 3 % -5 && (-2 + 7 * -3) % 7 == -2 % 7
