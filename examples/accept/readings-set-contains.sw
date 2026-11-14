-- `Set.contains` and `Set.fromList` tests read as membership: a fact is taken
-- apart, built and `.read` like any test with a reading (SW-3094).
import Std (Bool, Eq, List, Map, Nat, Set)

theorem readsMember ∀ (s: Set Nat) (x: Nat) (h: s.contains x): x ∈ s.toList := h.read

theorem readsNotMember ∀ (s: Set Nat) (x: Nat) (h: s.contains x = False): x ∉ s.toList := h.read

theorem readsFromList ∀ (xs: List Nat) (x: Nat) (h: (Set.fromList xs).contains x): x ∈ xs :=
  (Set.memToListFromList xs x).forward h.read

theorem partsOfAnd ∀ (a: Bool) (s: Set Nat) (x: Nat) (h: (a && s.contains x) = True): a = True := match h with
  | Both ha hx => ha

theorem andMember ∀ (a: Bool) (s: Set Nat) (x: Nat) (h: (a && s.contains x) = True): x ∈ s.toList := match h with
  | Both ha hx => hx.read

theorem mapKey ∀ (m: Map Nat Nat) (x: Nat) (h: m.contains x): x ∈ m.keys := h.read

theorem mapNoKey ∀ (m: Map Nat Nat) (x: Nat) (h: m.contains x = False): x ∉ m.keys := h.read
