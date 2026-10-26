-- expect-error: E-REWRITE-NOTHING
-- `Nat.addZero`'s pattern `n + 0` occurs only inside the body of the opaque
-- `plusZero`, so `rewrite` finds nothing: the error says `plusZero` is
-- opaque. (docs/proposals/opaque-definitions.md §6.10.)
import Std (Nat)

opaque def plusZero (n: Nat): Nat := n + 0

theorem useIt (n: Nat): plusZero n = n :=
  rewrite Nat.addZero n in rfl
