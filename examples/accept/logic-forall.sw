-- `forall (x: T) => P`, or `∀ (x: T) => P`, is the function type `(x: T) ->
-- P` (D3458): the same term, so the same hash, whichever is written. Like
-- `exists`, it takes several parameters, and its body runs to the end of
-- the expression.
import Std (Exists, Nat)
import Std.Exists (Witness)

theorem plusZero: ∀ (n: Nat) => n + 0 = n := n => rfl

theorem plusZeroAscii: forall (n: Nat) => n + 0 = n := plusZero

theorem plusZeroArrow: (n: Nat) -> n + 0 = n := plusZero

-- A quantified hypothesis, used at the values it's needed at.
theorem twice ∀ (p: Nat -> Prop) (all: ∀ (n: Nat) => p n): p 1 ∧ p 2 := Both (all 1) (all 2)

-- A group of names shares a type; implicit parameters are written in
-- brackets, as in a header; a bare name's type is inferred.
theorem swapped ∀ (comm: ∀ (a b: Nat) => a + b = b + a): 2 + 3 = 3 + 2 := comm 2 3

theorem sameLength ∀ (h: ∀ [a: Type] (xs: List a) => xs.length = xs.length): [1, 2].length = 2 := h [1, 2]

theorem inferred ∀ (h: ∀ n => n * 1 = n): 7 * 1 = 7 := h 7

-- The body takes the rest: an `->` in it is an implication under the `∀`.
theorem positive: ∀ (n: Nat) => n > 0 -> n ≥ 1 := n => h => omega

-- After `&&`, `||` and `<->`, as `exists` may.
theorem both: 1 = 1 && ∀ (n: Nat) => n = n := Both rfl (n => rfl)

-- `∀` and `∃` together.
theorem successor: ∀ (n: Nat) => ∃ (m: Nat) => m = n + 1 := n => Witness (n + 1) rfl
