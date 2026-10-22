-- expect-error: E-OMEGA
-- A fact `Not (x = y)` is not used, so this needs a case split that `omega` does not make.
import Std (Nat)

theorem neq (x: Nat) (y: Nat) (h: Not (x = y)) (h2: x <= y): x < y := omega
