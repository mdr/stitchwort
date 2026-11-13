-- Probe for docs/proposals/bool-as-proposition.md §2: what is refused today.
-- Every declaration FAILS: E-NOT-A-TYPE three times, E-TYPE-MISMATCH, E-CASES.
import Std (Bool, Nat, List)

theorem bare ∀ (b: Bool) (h: b): b = True := h
theorem negated ∀ (a: Bool) (h: ¬a): a = False := ?
theorem conjunction ∀ (a b: Bool) (h: a ∧ b): a = True := ?

theorem takeApart ∀ (a b c: Bool) (h: (a && (b || c)) = True): b = True ∨ c = True := match h with
  | Both ha (Inl hb) => Inl hb
  | Both ha (Inr hc) => Inr hc

theorem clash ∀ (a: Bool) (h: a = True) (k: a = False): Void := cases
