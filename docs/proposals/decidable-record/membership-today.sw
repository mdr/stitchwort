-- Baseline for membership.sw: the same fact through today's `Decidable`,
-- the decision and its proofs computed by the kernel. Checks, in 2.2 s
-- (10.4 s through `byDecision`, which also runs the decision while elaborating).
import Std (Bool, Decidable, List, Nat)
theorem far: 299 ∈ List.range 0 300 := Decidable.fromYes (List.decMem 299 (List.range 0 300)) Trivial
