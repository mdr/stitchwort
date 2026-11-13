--| `Int` lemmas proved with `omega` and `ring`: sizes of products, and
--| division and remainders by a divisor that isn't a constant.
-- They live here, not in `Int/Int.sw`, which `omega` itself needs.

--| `|x * y| = |x| * |y|`.
theorem Int.natAbsMul ∀ (x y: Int): Int.natAbs (x * y) = Int.natAbs x * Int.natAbs y := match x, y with
  | OfNat m, OfNat n => rfl
  | OfNat m, NegSucc n => Int.natAbsNeg (OfNat (m * Succ n))
  | NegSucc m, OfNat n => Int.natAbsNeg (OfNat (Succ m * n))
  | NegSucc m, NegSucc n => rfl

--| Only 0 has size 0.
theorem Int.natAbsZero ∀ (x: Int) (h: Int.natAbs x = 0): x = 0 := match x with
  | OfNat n => Eq.cong OfNat h
  | NegSucc n => Void.exfalso (Nat.succNotZero n h)

--| The size of `x` as an `Int` is `x` or `-x`.
theorem Int.natAbsCases ∀ (x: Int): (Nat.toInt (Int.natAbs x) = x) ∨ (Nat.toInt (Int.natAbs x) = 0 - x) :=
  match x with
    | OfNat n => Inl rfl
    | NegSucc n => Inr rfl

-- Sizes. `omega` knows what `Int.natAbs x` is (`Int.natAbsDichotomy`), so
-- each of these is `omega`; they're stated for `rewrite` and for listing
-- as facts where the goal's terms only match after rewriting.

--| `x ≤ |x|`.
theorem Int.leNatAbs ∀ (x: Int): x ≤ Nat.toInt (Int.natAbs x) := omega

--| `-x ≤ |x|`.
theorem Int.negLeNatAbs ∀ (x: Int): 0 - x ≤ Nat.toInt (Int.natAbs x) := omega

--| `|x| = x` for `x` that isn't negative.
theorem Int.natAbsOfNonneg ∀ (x: Int) (nonneg: 0 ≤ x): Nat.toInt (Int.natAbs x) = x := omega

--| `|x| = -x` for negative `x`.
theorem Int.natAbsOfNeg ∀ (x: Int) (neg: x < 0): Nat.toInt (Int.natAbs x) = 0 - x := omega

--| `|-x| = |x|`, with `-x` written `0 - x` (`Int.natAbsNeg` is the same for
--| `Int.neg x`).
theorem Int.natAbsNegate ∀ (x: Int): Int.natAbs (0 - x) = Int.natAbs x := omega

--| `|x - y| = |y - x|`.
theorem Int.natAbsSubComm ∀ (x: Int) (y: Int): Int.natAbs (x - y) = Int.natAbs (y - x) := omega

--| The triangle inequality, `|x + y| ≤ |x| + |y|` (Lean's `Int.natAbs_add_le`).
theorem Int.natAbsAdd ∀ (x: Int) (y: Int): Int.natAbs (x + y) ≤ Int.natAbs x + Int.natAbs y := omega

--| `|x - y| ≤ |x| + |y|` (Lean's `Int.natAbs_sub_le`).
theorem Int.natAbsSubLe ∀ (x: Int) (y: Int): Int.natAbs (x - y) ≤ Int.natAbs x + Int.natAbs y := omega

--| The triangle inequality for distances: going from `a` to `c` by way of
--| `b` is no shorter, `|a - c| ≤ |a - b| + |b - c|`.
theorem Int.natAbsTriangle ∀ (a: Int) (b: Int) (c: Int): Int.natAbs (a - c) ≤ Int.natAbs (a - b) + Int.natAbs (b - c) := omega

--| The reverse triangle inequality, `|x| - |y| ≤ |x - y|`, with `Nat`
--| subtraction on the left (so it's 0 when `|x| ≤ |y|`).
theorem Int.natAbsSubNatAbs ∀ (x: Int) (y: Int): Int.natAbs x - Int.natAbs y ≤ Int.natAbs (x - y) := omega

--| Only 1 and -1 square to 1, and both have size 1.
theorem Int.natAbsOfMulSelfOne ∀ (x: Int) (square: x * x = 1): Int.natAbs x = 1 :=
  Nat.mulSelfOne (Int.natAbs x) (omega [Int.mulSelf x])

--| A number between `-|d|` and `|d|`, exclusive, is smaller in size than
--| `d`.
theorem Int.natAbsLt ∀ (x: Int) (d: Int) (low: 0 - Nat.toInt (Int.natAbs d) < x) (high: x < Nat.toInt (Int.natAbs d)):
    Int.natAbs x < Int.natAbs d := match Int.natAbsCases x with
      | Inl same => omega
      | Inr opposite => omega

--| A multiple of `d` smaller in size than `d` is 0 times `d`.
theorem Int.smallMultiple ∀ (d: Int) (k: Int) (nonzero: d ≠ 0) (small: Int.natAbs (d * k) < Int.natAbs d): k = 0 :=
  let sizes: Int.natAbs d * Int.natAbs k < Int.natAbs d := rewrite <- Int.natAbsMul d k in small
  let positive: Int.natAbs d ≠ 0 := zero => nonzero (Int.natAbsZero d zero)
  match size: Int.natAbs k with
    | Zero => Int.natAbsZero k size
    | Succ j => Void.exfalso (omega [Nat.leMulPos (Int.natAbs d) (Int.natAbs k) (omega)])

--| Two quotients and remainders of the same number by `d`, each remainder
--| from 0 up to below `|d|`, are the same.
theorem Int.divModUniqueOf ∀ (d: Int) (quotient: Int) (remainder: Int) (other: Int) (otherRemainder: Int) (nonzero: d ≠ 0)
    (same: d * quotient + remainder = d * other + otherRemainder) (low: 0 ≤ remainder) (high: remainder < Nat.toInt (Int.natAbs d))
    (otherLow: 0 ≤ otherRemainder) (otherHigh: otherRemainder < Nat.toInt (Int.natAbs d)): (quotient = other) ∧ (remainder = otherRemainder) :=
  let difference: d * (quotient - other) = otherRemainder - remainder := ring [same]
  let small: Int.natAbs (d * (quotient - other)) < Int.natAbs d := rewrite difference in Int.natAbsLt (otherRemainder - remainder) d (omega) (omega)
  let zero: quotient - other = 0 := Int.smallMultiple d (quotient - other) nonzero small
  let none: d * (quotient - other) = 0 := ring [d * zero]
  Both (omega) (omega [difference, none])

--| The quotient and remainder are the only ones with the division law and a
--| remainder from 0 up to below `|d|` (so `d` isn't 0).
theorem Int.divModUnique ∀ (a: Int) (d: Int) (quotient: Int) (remainder: Int) (law: d * quotient + remainder = a)
    (low: 0 ≤ remainder) (high: remainder < Nat.toInt (Int.natAbs d)): (a / d = quotient) ∧ (a % d = remainder) :=
  let ok: d ≠ 0 := zero => Void.exfalso (omega [rewrite zero at high in high])
  Int.divModUniqueOf d (a / d) (a % d) quotient remainder ok (Eq.trans (Int.divAddMod a d) (Eq.sym law))
    (Int.modNonneg a d) (Int.modLtAbs a d) low high

--| A nonzero integer has a nonzero size.
theorem Int.natAbsPos ∀ (d: Int) (nonzero: d ≠ 0): 0 < Int.natAbs d :=
  let positive: Int.natAbs d ≠ 0 := zero => nonzero (Int.natAbsZero d zero)
  omega

--| `(d * a) / d = a` for a nonzero `d` (Lean's `Int.mul_ediv_cancel_left`).
theorem Int.mulDivCancel ∀ (d: Int) (a: Int) [auto ok: d ≠ 0]: (d * a) / d = a :=
  let positive := Int.natAbsPos d ok
  And.left (Int.divModUnique (d * a) d a 0 (ring) (omega) (omega))

--| With `x = d * quotient + remainder`, adding `d * q` adds `q` to the
--| quotient.
theorem Int.addMulRegroup ∀ (x: Int) (d: Int) (q: Int) (quotient: Int) (remainder: Int) (law: d * quotient + remainder = x):
    d * (quotient + q) + remainder = x + d * q :=
  ring [law]

--| Adding a multiple of `d`, a negative one too, keeps the remainder (Lean's
--| `Int.add_mul_emod_self_left`).
theorem Int.modAddMul ∀ (x: Int) (d: Int) (q: Int): (x + d * q) % d = x % d :=
  if zero: d = 0 then rewrite zero, Int.zeroMul q, Int.addZero x in rfl
  else
    And.right (Int.divModUnique (x + d * q) d (x / d + q) (x % d) (Int.addMulRegroup x d q (x / d) (x % d) (Int.divAddMod x d))
      (Int.modNonneg x d) (Int.modLtAbs x d))

--| With `x = d * quotient + remainder`, the remainder plus `y` is `x + y`
--| less `d * quotient`.
theorem Int.remainderAddRegroup ∀ (x: Int) (y: Int) (d: Int) (quotient: Int) (remainder: Int) (law: d * quotient + remainder = x):
    remainder + y = (x + y) + d * (0 - quotient) :=
  ring [law]

--| Only the remainder of `x` matters to the remainder of `x + y` (Lean's
--| `Int.emod_add_emod`).
theorem Int.modModAdd ∀ (x: Int) (y: Int) (d: Int): (x % d + y) % d = (x + y) % d :=
  rewrite Int.remainderAddRegroup x y d (x / d) (x % d) (Int.divAddMod x d)
  in Int.modAddMul (x + y) d (0 - x / d)

--| `a - b = 0` means `a = b`.
theorem Int.subEqZero ∀ (a: Int) (b: Int) (h: a - b = 0): a = b := omega

theorem Int.negOfNatZero ∀ (k: Nat) (h: Int.neg (OfNat k) = 0): k = 0 := omega

--| No zero divisors (Lean's `Int.mul_eq_zero`).
theorem Int.mulEqZero ∀ (a b: Int) (h: a * b = 0): (a = 0) ∨ (b = 0) := match a, b with
  | OfNat m, OfNat n =>
    match Nat.mulEqZero m n (Int.ofNatInjective (m * n) 0 h) with
      | Inl z => Inl (Eq.cong OfNat z)
      | Inr z => Inr (Eq.cong OfNat z)
  | OfNat m, NegSucc n =>
    match Nat.mulEqZero m (Succ n) (Int.negOfNatZero (m * Succ n) h) with
      | Inl z => Inl (Eq.cong OfNat z)
      | Inr z => Void.exfalso (omega [z])
  | NegSucc m, OfNat n =>
    match Nat.mulEqZero (Succ m) n (Int.negOfNatZero (Succ m * n) h) with
      | Inl z => Void.exfalso (omega [z])
      | Inr z => Inr (Eq.cong OfNat z)
  | NegSucc m, NegSucc n =>
    match Nat.mulEqZero (Succ m) (Succ n) (Int.ofNatInjective (Succ m * Succ n) 0 h) with
      | Inl z => Void.exfalso (omega [z])
      | Inr z => Void.exfalso (omega [z])

--| A nonzero factor cancels (Lean's `Int.mul_left_cancel`).
theorem Int.mulCancelLeft ∀ (c: Int) (a: Int) (b: Int) (nonzero: c ≠ 0) (h: c * a = c * b): a = b :=
  match Int.mulEqZero c (a - b) (calc c * (a - b)
      _ = c * a - c * b := ring
      _ = c * b - c * b := rewrite h
      _ = 0 := ring) with
    | Inl z => Void.exfalso (nonzero z)
    | Inr z => Int.subEqZero a b z

--| A square is the square of the size.
theorem Int.mulSelf ∀ (x: Int): x * x = OfNat (Int.natAbs x * Int.natAbs x) := match x with
  | OfNat n => rfl
  | NegSucc n => rfl

--| Two squares add up to 0 only when both are 0.
theorem Int.sumSquaresZero ∀ (x: Int) (y: Int) (h: x * x + y * y = 0): (x = 0) ∧ (y = 0) :=
  let natural: Int.natAbs x * Int.natAbs x + Int.natAbs y * Int.natAbs y = 0 :=
    Int.ofNatInjective _ 0 (rewrite Int.mulSelf x, Int.mulSelf y at h in h)
  Both (Int.natAbsZero x (Nat.mulSelfZero (Int.natAbs x) (omega))) (Int.natAbsZero y (Nat.mulSelfZero (Int.natAbs y) (omega)))

--| Equal squares: the same number, or its negation.
theorem Int.squaresEq ∀ (x: Int) (y: Int) (h: x * x = y * y): (x = y) ∨ (x + y = 0) :=
  match Int.mulEqZero (x - y) (x + y) (ring [h]) with
    | Inl z => Inl (Int.subEqZero x y z)
    | Inr z => Inr z

test "Int.mulEqZero" := (0 * -3 == 0) && (-4 * 5 != 0)
test "Int.mulDivCancel" := (-7 * 13) / -7 == 13 && (5 * -4) / 5 == -4
test "Int.modAddMul" := (3 + -5 * 4) % -5 == 3 % -5 && (-2 + 7 * -3) % 7 == -2 % 7

-- `Int.toNatChecked`, signs, and wrapping with `Int.modNat`.

--| A number that `toNatChecked` takes is that number.
theorem Int.toNatCheckedSome ∀ (x: Int) (n: Nat) (checked: x.toNatChecked = Some n): x = n.toInt := match x with
  | OfNat m => Eq.cong OfNat (Option.someInjective checked)

--| A number that `toNatChecked` refuses is negative.
theorem Int.toNatCheckedNone ∀ (x: Int) (checked: x.toNatChecked = None): x < 0 := match x with
  | NegSucc m => omega

--| `|x|` is `x` times its sign.
theorem Int.natAbsSign ∀ (x: Int): x.natAbs.toInt = x.sign * x := match x with
  | OfNat Zero => rfl
  | OfNat (Succ n) => Eq.cong OfNat (omega)
  | NegSucc n => Eq.cong OfNat (omega)

--| What `Int.sign` is, by the three cases for the sign of `x`.
theorem Int.signCases ∀ (x: Int): (x.sign = 1 ∧ 0 < x) ∨ (x.sign = 0 ∧ x = 0) ∨ (x.sign = -1 ∧ x < 0) :=
  match x with
    | OfNat 0 => Inr (Inl (Both rfl rfl))
    | OfNat (Succ k) => Inl (Both rfl (omega))
    | NegSucc k => Inr (Inr (Both rfl (omega)))

--| The product of two consecutive integers is never negative.
theorem Int.mulNonnegSucc ∀ (d: Int): 0 ≤ d * (d + 1) := match e: Int.leq 0 d with
  | True => Int.mulNonneg d (d + 1) (omega) (omega)
  | False =>
    let flipped: d * (d + 1) = (-d) * (-d - 1) := ring
    omega [Int.mulNonneg (-d) (-d - 1) (omega) (omega)]

--| Scaling a count kept only when `b` holds: `v` times the kept count is the
--| count times `v` when `b` holds, else 0.
theorem Int.mulKeepIf ∀ (v: Int) (x: Nat) (b: Bool): v * (x.keepIf b).toInt = x.toInt * (if b then v else 0) :=
  match b with
    | True => ring
    | False => ring

--| Dividing a multiple of a positive number by it: if `|value|` is `times`
--| times `Succ below`, then `Succ below` times `value / Succ below` is `value`.
theorem Int.divExact ∀ (value: Int) (below times: Nat) (multiple: value.natAbs = times * Succ below):
    (Succ below).toInt * (value / (Succ below).toInt) = value := match value, times with
      | OfNat n, times =>
        let quotient := Nat.divUnique n (Succ below) times 0 (omega) (rewrite multiple in ring)
        rewrite quotient in Eq.cong OfNat (rewrite multiple in ring)
      | NegSucc m, Zero => Void.exfalso (omega [multiple])
      | NegSucc m, Succ times =>
        let whole: m = times * Succ below + below := omega [multiple, (ring: Succ times * Succ below = times * Succ below + Succ below)]
        let quotient := Nat.divUnique m (Succ below) times below (omega) whole
        rewrite quotient in Eq.cong NegSucc (omega [whole, (ring: times + below * Succ times = times * Succ below + below)])

--| A number below `size` wraps to itself.
theorem Int.modNatOfLt ∀ (size x: Nat) (inside: x < size): x.toInt.modNat size = x := match size with
  | Succ n => Nat.modSmall x (Succ n) inside

--| One step forward on a line of `size` is adding 1 and wrapping: the
--| conditional that goes back to 0 at the end is `modNat`.
theorem Int.modNatSuccWrap ∀ (size x: Nat) (inside: x < size):
    (if x + 1 == size then 0 else x + 1) = Int.modNat (x.toInt + 1) size := match size with
      | Succ n =>
        match e: x + 1 == Succ n with
          | True => rewrite (omega [e.read]: x = n) in Eq.sym (Nat.modSelf (Succ n))
          | False => Eq.sym (Nat.modSmall (x + 1) (Succ n) omega)

--| One step back on a line of `size` is subtracting 1 and wrapping: the
--| conditional that goes to the end from 0 is `modNat`.
theorem Int.modNatPredWrap ∀ (size x: Nat) (inside: x < size):
    (if x == 0 then size - 1 else x - 1) = Int.modNat (x.toInt - 1) size := match size, x with
      | Succ n, Zero => rfl
      | Succ n, Succ x =>
        rewrite (omega: (Succ x).toInt - 1 = x.toInt) in Eq.sym (Nat.modSmall x (Succ n) omega)

--| On a line of `size`, `size * laps` more steps of any `velocity` land
--| where they did.
theorem Int.modNatPeriodic ∀ (size: Nat) (laps: Nat) (start: Int) (seconds: Nat) (velocity: Int):
    Int.modNat (start + velocity * (seconds + size * laps).toInt) size = Int.modNat (start + velocity * seconds.toInt) size :=
  rewrite (ring: start + velocity * (seconds + size * laps).toInt = start + velocity * seconds.toInt + size.toInt * (laps.toInt * velocity))
  in Int.modNatAddMulInt (start + velocity * seconds.toInt) size (laps.toInt * velocity)

test "Int.toNatCheckedSome, Int.toNatCheckedNone" := (5: Int).toNatChecked == Some 5 ∧ (-5: Int).toNatChecked == None
test "Int.natAbsSign" := (-7: Int).natAbs.toInt == (-7: Int).sign * -7 ∧ (4: Int).natAbs.toInt == (4: Int).sign * 4
test "Int.mulNonnegSucc" := 0 ≤ (-4: Int) * (-4 + 1) ∧ 0 ≤ (3: Int) * (3 + 1)
test "Int.mulKeepIf" := (-3: Int) * (Nat.keepIf 4 True).toInt == (4: Nat).toInt * -3 ∧ (-3: Int) * (Nat.keepIf 4 False).toInt == (4: Nat).toInt * 0
test "Int.divExact" := (3: Nat).toInt * (-12 / (3: Nat).toInt) == -12
test "Int.modNatOfLt" := Int.modNat (2: Nat).toInt 5 == 2
test "Int.modNatSuccWrap, Int.modNatPredWrap" := (if 4 + 1 == 5 then 0 else 4 + 1) == Int.modNat ((4: Nat).toInt + 1) 5 ∧ (if 0 == 0 then 5 - 1 else 0 - 1) == Int.modNat ((0: Nat).toInt - 1) 5
test "Int.modNatPeriodic" := Std.Int.modNat (2 + -3 * (1 + 5 * 4: Nat).toInt) 5 == Std.Int.modNat (2 + -3 * (1: Nat).toInt) 5
