-- expect-error: E-TUPLE-PARTS
-- A tuple proving `∃ n => A ∧ B` has three parts; the parts are counted
-- from the outside, one per binder and one per conjunct.
import Std (byDecision)

theorem small: ∃ (n: Nat) => n > 2 ∧ n * n = 49 := (7, byDecision, byComputing, byComputing)
