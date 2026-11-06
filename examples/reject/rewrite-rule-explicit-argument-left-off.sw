-- expect-error: E-REWRITE-RULE
-- `Nat.oneMul`'s `n` is explicit and left off: the left side `1 * n` computes
-- to that unknown, so the note names the argument rather than implicit ones.
import Std (Nat)

theorem t (n: Nat): 1 * n + 0 = n :=
  rewrite Nat.oneMul in Nat.addZero n
