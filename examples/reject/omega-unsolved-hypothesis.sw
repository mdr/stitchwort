-- expect-error: E-OMEGA
-- `omega` inside a lambda whose parameter's type is still unsolved: `same`
-- can't be read as a fact yet, so the failure names it rather than leaving
-- it out of the facts silently. `DecEq.trueOfNe` fixes a `List Nat` instance
-- only after the lambda is checked, so `same`'s type stays unknown here.
import Std (Bool, DecEq, Decidable, List, Nat, Void)

theorem unsolvedHypothesis (xs: List Nat) (ys: List Nat): ((xs != ys): Bool) = True :=
  DecEq.trueOfNe (same => (omega: Void))
