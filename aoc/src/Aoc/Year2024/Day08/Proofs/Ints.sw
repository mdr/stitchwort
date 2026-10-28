-- Integer facts the proofs need that std doesn't have: no zero divisors,
-- cancelling a nonzero factor, squares, and exact division. `omega` doesn't
-- work on `Int`, so each is by cases on the constructors, down to `Nat`.

namespace Aoc.Year2024.Day08.Proofs
import Std (And, Eq, Int, Nat, Or, Void)

-- `a - b = 0` means `a = b`.
theorem subEqZero (a: Int) (b: Int) (h: a - b = 0): a = b :=
  calc a
    _ = (a - b) + b := ring
    _ = 0 + b := rewrite h
    _ = b := ring

-- `0 * n` is the only way to get 0 from naturals.
theorem natMulEqZero: (m: Nat) → (n: Nat) → m * n = 0 → Or (m = 0) (n = 0)
  | Zero, n, h => Inl rfl
  | Succ m, Zero, h => Inr rfl
  | Succ m, Succ n, h => omega [Nat.leMulPos (Succ m) (Succ n) (omega)]

theorem negOfNatZero: (k: Nat) → Int.neg (OfNat k) = 0 → k = 0
  | Zero, h => rfl
  | Succ k, h => Void.exfalso (Int.negSuccNotOfNat k 0 h)

-- No zero divisors.
theorem mulEqZero: (a: Int) → (b: Int) → a * b = 0 → Or (a = 0) (b = 0)
  | OfNat m, OfNat n, h =>
    match natMulEqZero m n (Int.ofNatInjective (m * n) 0 h) with
      | Inl z => Inl (Eq.cong OfNat z)
      | Inr z => Inr (Eq.cong OfNat z)
  | OfNat m, NegSucc n, h =>
    match natMulEqZero m (Succ n) (negOfNatZero (m * Succ n) h) with
      | Inl z => Inl (Eq.cong OfNat z)
      | Inr z => Void.exfalso (omega [z])
  | NegSucc m, OfNat n, h =>
    match natMulEqZero (Succ m) n (negOfNatZero (Succ m * n) h) with
      | Inl z => Void.exfalso (omega [z])
      | Inr z => Inr (Eq.cong OfNat z)
  | NegSucc m, NegSucc n, h =>
    match natMulEqZero (Succ m) (Succ n) (Int.ofNatInjective (Succ m * Succ n) 0 h) with
      | Inl z => Void.exfalso (omega [z])
      | Inr z => Void.exfalso (omega [z])

-- A nonzero factor cancels.
theorem mulCancel (c: Int) (a: Int) (b: Int) (nonzero: Not (c = 0)) (h: c * a = c * b): a = b :=
  match mulEqZero c (a - b) (calc c * (a - b)
      _ = c * a - c * b := ring
      _ = c * b - c * b := rewrite h
      _ = 0 := ring) with
    | Inl z => Void.exfalso (nonzero z)
    | Inr z => subEqZero a b z

-- A square is the square of a natural number.
theorem mulSelf: (x: Int) → x * x = OfNat (Int.natAbs x * Int.natAbs x)
  | OfNat n => rfl
  | NegSucc n => rfl

theorem natAbsZero: (x: Int) → Int.natAbs x = 0 → x = 0
  | OfNat n, h => Eq.cong OfNat h
  | NegSucc n, h => Void.exfalso (omega [h])

theorem natMulSelfZero (n: Nat) (h: n * n = 0): n = 0 :=
  match natMulEqZero n n h with
    | Inl z => z
    | Inr z => z

-- Two squares add up to 0 only when both are 0.
theorem sumSquaresZero (x: Int) (y: Int) (h: x * x + y * y = 0): And (x = 0) (y = 0) :=
  let natural: Int.natAbs x * Int.natAbs x + Int.natAbs y * Int.natAbs y = 0 :=
    Int.ofNatInjective _ 0 (rewrite mulSelf x, mulSelf y at h in h)
  Both (natAbsZero x (natMulSelfZero (Int.natAbs x) (omega))) (natAbsZero y (natMulSelfZero (Int.natAbs y) (omega)))

-- Equal squares: the same number, or its negation.
theorem squaresEq (x: Int) (y: Int) (h: x * x = y * y): Or (x = y) (x + y = 0) :=
  match mulEqZero (x - y) (x + y) (ring [h]) with
    | Inl z => Inl (subEqZero x y z)
    | Inr z => Inr z

-- Dividing a multiple of 3 by 3.
theorem modThreeMul: (k: Int) → (3 * k) % 3 = 0
  | OfNat n => Eq.cong OfNat (omega)
  | NegSucc n => Eq.cong OfNat (omega)

theorem divThreeMul: (k: Int) → (3 * k) / 3 = k
  | OfNat n => Eq.cong OfNat (omega)
  | NegSucc n => Eq.cong NegSucc (omega)
