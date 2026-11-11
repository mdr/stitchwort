-- expect-error: E-OMEGA
-- `omega` inside a lambda whose parameter's type is still unsolved: `same`
-- can't be read as a fact yet, so the failure names it rather than leaving
-- it out of the facts silently.
import Std (Bool, DecEq, Decidable, Nat, Void)

theorem unsolvedHypothesis (a: Nat) (n: Nat): ((a + a != n): Bool) = True :=
  DecEq.trueOfNe (same => (omega: Void))
