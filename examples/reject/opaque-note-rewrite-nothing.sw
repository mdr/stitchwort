-- expect-error: E-REWRITE-NOTHING
-- `Nat.mulOne`'s pattern `n * 1` occurs only inside the body of the opaque
-- `timesOne`, so `rewrite` finds nothing: the error says `timesOne` is
-- opaque. (docs/proposals/opaque-definitions.md §6.10.)
import Std (Nat)

opaque def timesOne (n: Nat): Nat := n * 1

theorem useIt (n: Nat): timesOne n = n :=
  rewrite Nat.mulOne n in rfl
