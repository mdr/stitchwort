-- expect-error: E-OMEGA
-- A goal `omega` can't read as arithmetic is proved only when the facts
-- contradict each other; `seat < 5` doesn't.
import Std (Nat, List)

theorem noContradiction (seat: Nat) (rest: List Nat) (h: seat < 5): seat + 1 ∈ rest := omega
