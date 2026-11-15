-- What `auto` proves in a catch-all arm (docs/proposals/catch-all-facts.md):
-- after arms that match numbers, characters or texts, the argument is none
-- of those literals, so `x ≠ lit` is a goal `byDecision` or an `[auto]`
-- parameter solves there, though the fact is only a mark on the value, not
-- a hypothesis.
import Std (Bool, Int, Nat, Option, Text, byDecision)

-- A lemma that wants `k ≠ 5` as a value.
theorem notFiveIsZero ∀ (f: Nat → Nat) (hf: ∀ (k: Nat) (ne: k ≠ 5) => f k = 0) (n: Nat): (n = 5) ∨ (f n = 0) :=
  match n with
    | 5 => Inl rfl
    | m => Inr (hf m byDecision)

-- An `[auto]` parameter finds it without a word.
def apartFromFive (n: Nat) [auto ok: n ≠ 5]: Nat := n

def guarded (n: Nat): Nat := match n with
  | 5 => 0
  | m => apartFromFive m

-- Several literals above, and either side of `≠`.
theorem twoNumbers ∀ (n: Nat): (n ≠ 5 ∧ n ≠ 7) ∨ n = 5 ∨ n = 7 := match n with
  | 5 => Inr (Inl rfl)
  | 7 => Inr (Inr rfl)
  | m => Inl (Both byDecision byDecision)

theorem fiveOnTheLeft ∀ (n: Nat): 5 ≠ n ∨ n = 5 := match n with
  | 5 => Inr rfl
  | m => Inl byDecision

-- A literal alternative, and a pattern in one column of two.
theorem orPattern ∀ (n: Nat): (n ≠ 1 ∧ n ≠ 2) ∨ n ≤ 2 := match n with
  | 1 | 2 => Inr byDecision
  | m => Inl (Both byDecision byDecision)

theorem secondColumn ∀ (a b: Nat): a ≠ 0 ∨ a = 0 := match a, b with
  | 0, y => Inr rfl
  | x, 1 => Inl byDecision
  | x, y => Inl byDecision

-- Integers, within each sign.
theorem integers ∀ (n: Int): (n ≠ 3 ∧ n ≠ (-2)) ∨ n = 3 ∨ n = (-2) := match n with
  | 3 => Inr (Inl rfl)
  | (-2) => Inr (Inr rfl)
  | m => Inl (Both byDecision byDecision)

-- Characters.
theorem character ∀ (c: Char): c ≠ 'k' ∨ c = 'k' := match c with
  | 'k' => Inr rfl
  | d => Inl byDecision

-- Texts, split character by character in the arm, which is checked in
-- every case.
theorem texts ∀ (s: Text): (s ≠ "ab" ∧ s ≠ "ac") ∨ s = "ab" ∨ s = "ac" := match s with
  | "ab" => Inr (Inl rfl)
  | "ac" => Inr (Inr rfl)
  | t => Inl (Both byDecision byDecision)

-- An arm with a condition above gives no fact: the catch-all is reached
-- with `n = 5` when the condition fails, so only 6 is ruled out.
theorem afterGuard ∀ (n: Nat) (b: Bool): n ≠ 6 ∨ n = 6 := match n with
  | 5 if b => Inl byDecision
  | 6 => Inr rfl
  | m => Inl byDecision

-- The fact reaches goals that only contain the variable: `n + 2`, `Some n`,
-- `(n, c)`.
theorem sum ∀ (n: Nat): n + 2 ≠ 7 ∨ n = 5 := match n with
  | 5 => Inr rfl
  | m => Inl byDecision

theorem wrapped ∀ (n: Nat): Some n ≠ Some 5 ∨ n = 5 := match n with
  | 5 => Inr rfl
  | m => Inl byDecision

theorem pair ∀ (n: Nat) (c: Char): (n, c) ≠ (5, 'x') ∨ n = 5 := match n with
  | 5 => Inr rfl
  | m => Inl byDecision
