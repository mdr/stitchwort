-- `any` and `all` read as what they test (docs/proposals/bool-as-proposition.md
-- §5.1), though they take an effect row: their readings are stated with a
-- pure `p`, as every test fact of theirs has.
import Std (Array, Bool, Eq, List, Nat, NonEmptyList, Text)

theorem someBig (xs: List Nat) (h: xs.any (x => x > 2)): ∃ (x: Nat) => x ∈ xs ∧ x > 2 := h.read

theorem someBigWitness (xs: List Nat) (h: xs.any (x => x > 2)): ∃ (x: Nat) => x > 2 := match h with
  | Witness x found => Witness x found.right

theorem noneBig (xs: List Nat) (h: xs.any (x => x > 2) = False) (x: Nat) (m: x ∈ xs): (x > 2) = False := h.read x m

theorem allSmall (xs: List Nat) (h: xs.all (x => x < 5)) (x: Nat) (m: x ∈ xs): x < 5 := h.read x m

theorem notAllSmall (xs: List Nat) (h: xs.all (x => x < 5) = False): ∃ (x: Nat) => x ∈ xs ∧ (x < 5) = False := h.read

-- Built from the proposition: a constructor checked against the test fact.
theorem builtAny (xs: List Nat) (m: 3 ∈ xs): xs.any (x => x > 2) := Witness 3 (Both m rfl)

-- The wrappers unfold to `List.any` and `List.all`, which have the readings.
theorem arrayAny (a: Array Nat) (h: a.any (x => x > 2)): ∃ (x: Nat) => x ∈ a.toList ∧ x > 2 := h.read

theorem nonEmptyAll (xs: NonEmptyList Nat) (h: xs.all (x => x < 5)) (x: Nat) (m: x ∈ xs.toList): x < 5 := h.read x m

theorem textAny (t: Text) (h: t.any (c => c == 'a')): ∃ (c: Char) => c ∈ t.toList ∧ c == 'a' := h.read
