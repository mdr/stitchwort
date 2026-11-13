-- The comparison tests and the other std tests that had no reading now read
-- as their propositions, at both polarities (docs/proposals/
-- bool-as-proposition.md §5 and §11): `Nat.leq` and `Int.leq`/`Int.less`
-- (what `<=`, `<`, `>` and `>=` compute to), `List.inRange`,
-- `Nat.divides`, `List.isDistinct`, and `contains` on a list and on a
-- `NonEmptyList`.
import Std (Bool, Int, List, Nat, NonEmptyList)

-- `.read`: a comparison that failed is the opposite comparison.
theorem lessOfNotLessEq ∀ (x y: Nat) (h: (x <= y) = False): y < x := h.read

theorem lessEqOfNotLess ∀ (x y: Int) (h: (x < y) = False): y ≤ x := h.read

theorem lessEqSame ∀ (x y: Int) (h: (x >= y) = True): y ≤ x := h.read

-- `auto` reaches the same facts through the context.
def below (x y: Nat) [auto ok: x < y]: Nat := y - x

def belowInt (x y: Int) [auto ok: x < y]: Int := y - x

def absent (x: Nat) (xs: List Nat) [auto ok: x ∉ xs]: Nat := x

def afterFailed (x y: Nat) (h: (y <= x) = False): Nat := below x y

def afterFailedInt (x y: Int) (h: (y <= x) = False): Int := belowInt x y

def afterMissing (x: Nat) (xs: List Nat) (h: xs.contains x = False): Nat := absent x xs

test "after failed" := afterFailed 2 5 rfl == 3 ∧ afterFailedInt 2 5 rfl == 3

test "after missing" := afterMissing 4 [1, 2] rfl == 4

-- A list that doesn't contain `x`.
theorem notIn ∀ (x: Nat) (xs: List Nat) (h: xs.contains x = False): x ∉ xs := h.read

theorem notInNonEmpty ∀ (x: Nat) (xs: NonEmptyList Nat) (h: xs.contains x = False): ¬(NonEmptyList.Mem x xs) := h.read

theorem inNonEmpty ∀ (x: Nat) (xs: NonEmptyList Nat) (h: xs.contains x = True): NonEmptyList.Mem x xs := h.read

theorem bounds ∀ (x lo hi: Nat) (h: List.inRange x lo hi = True): lo ≤ x < hi := h.read

theorem outside ∀ (x lo hi: Nat) (h: List.inRange x lo hi = False): ¬(lo ≤ x < hi) := h.read

theorem multiple ∀ (d n: Nat) (h: Nat.divides d n = True): ∃ (t: Nat) => n = t * d := h.read

theorem notMultiple ∀ (d n: Nat) (h: Nat.divides d n = False): ¬(∃ (t: Nat) => n = t * d) := h.read

theorem repeats ∀ (xs: List Nat) (h: xs.isDistinct = False): ¬(List.Distinct xs) := h.read

-- A pattern reads the bounds as the `∧` they are.
theorem lowBound ∀ (x lo hi: Nat) (h: List.inRange x lo hi = True): lo ≤ x := match h with
  | Both low high => low
