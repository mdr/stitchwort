-- Facts the proofs need that std doesn't have: dividing a multiple of a
-- nonzero integer by it, and the least element of a list whose elements
-- are all the same.

namespace Aoc.Year2024.Day13.Proofs
import Aoc.Year2024.Day08.Proofs (natAbsMul, natAbsZero)
import Std (And, Eq, Int, List, Nat, Option, Or, Ord, Void)

-- A non-negative integer is the natural number of its size.
theorem ofNatAbs: (x: Int) → 0 ≤ x → x = Nat.toInt (Int.natAbs x)
  | OfNat n, h => rfl
  | NegSucc n, h => Void.exfalso (omega)

-- A multiple of `d` from 0 up to below `|d|` is 0 times `d`.
theorem smallMultiple (d: Int) (k: Int) (nonzero: d ≠ 0) (low: 0 ≤ d * k) (high: d * k < Nat.toInt (Int.natAbs d)): k = 0 :=
  let sizes: Int.natAbs d * Int.natAbs k < Int.natAbs d := rewrite <- natAbsMul d k in omega [ofNatAbs (d * k) low]
  match size: Int.natAbs k with
    | Zero => natAbsZero k size
    | Succ j => Void.exfalso (omega [Nat.leMulPos (Int.natAbs d) (Int.natAbs k) (omega)])

-- A quotient and remainder of `d * a` by `d`, with the remainder from 0 up
-- to below `|d|`: the quotient is `a`.
theorem quotientOfMultiple (d: Int) (a: Int) (quotient: Int) (remainder: Int) (nonzero: d ≠ 0) (law: d * quotient + remainder = d * a)
    (low: 0 ≤ remainder) (high: remainder < Nat.toInt (Int.natAbs d)): quotient = a :=
  let remainderIsMultiple: remainder = d * (a - quotient) := ring [law]
  omega [smallMultiple d (a - quotient) nonzero (rewrite <- remainderIsMultiple in low) (rewrite <- remainderIsMultiple in high)]

-- `(d * a) / d = a` for a nonzero `d`.
theorem mulDivCancel (d: Int) (a: Int) (nonzero: d ≠ 0): (d * a) / d = a :=
  quotientOfMultiple d a ((d * a) / d) ((d * a) % d) nonzero (Int.divAddMod (d * a) d) (Int.modNonneg (d * a) d) (Int.modLtAbs (d * a) d)

theorem minSelf (n: Nat): Ord.min n n = n := cases

-- The least of a list whose elements are all `least`, folding from `least`.
theorem foldMinAll (least: Nat): (xs: List Nat) → ((x: Nat) → x ∈ xs → x = least) → List.foldLeft xs least Ord.min = least
  | Nil, all => rfl
  | Cons x rest, all =>
    rewrite all x (Inl rfl), minSelf least in foldMinAll least rest (y member => all y (Inr member))

-- The least of a list that holds `least` and nothing else is `least`.
theorem minimumAllEqual (least: Nat): (xs: List Nat) → least ∈ xs → ((x: Nat) → x ∈ xs → x = least) → List.minimum xs = Some least
  | Nil, member, all => Void.exfalso member
  | Cons x rest, member, all =>
    rewrite all x (Inl rfl) in Eq.cong Some (foldMinAll least rest (y member => all y (Inr member)))

-- An empty list has no least element.
theorem minimumEmpty: (xs: List Nat) → ((x: Nat) → x ∈ xs → Void) → List.minimum xs = None
  | Nil, none => rfl
  | Cons x rest, none => Void.exfalso (none x (Inl rfl))
