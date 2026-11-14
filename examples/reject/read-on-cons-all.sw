-- expect-error: E-NOT-A-FUNCTION
-- `[d, ..more].all p` reads as `p d ∧ more.all p`, not as the `∀`, so
-- `.read x m` on it isn't a function; the error says to take it apart.
import Std (List, Nat)

theorem fromCons ∀ (d: Nat) (more: List Nat) (h: [d, ..more].all (x => x < 5)) (x: Nat) (m: x ∈ [d, ..more]): x < 5 :=
  h.read x m
