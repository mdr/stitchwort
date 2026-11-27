-- Fuzz elab batch 67 (SEED=0x26112643, case 3455, from accept/build-eight.sw),
-- reduced by Overmind: a conjunct `d.contains` with no argument. Expected
-- E-NOT-A-TYPE promptly; with four full conjuncts before it the check runs
-- past 60 s (300 s unreduced, ~284 MB, no E-RESOURCE). SW-4931.
import Std (Bool, List, Nat)

theorem t ∀ (x: Nat)  (a: List Nat) (ma: x ∈ a) (b: List Nat) (mb: x ∈ b) (c: List Nat) (mc: x ∈ c) (d: List Nat) (md: x ∈ d) (h: List Nat) (mh: x ∈ h):
    a.contains x ∧ b.contains x ∧ c.contains x ∧ d.contains    ∧ h.contains x :=
  Both ma (Both mb (Both mc (Both md (mh))))
