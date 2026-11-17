-- A `then` that ends its line takes the lines below it, at the block's own
-- column, as its body: a `let` there doesn't start a new statement of the
-- block (SW-3733).
import Std (Nat)

theorem zeroAdd ∀ (n: Nat) (h: n = 1): n + 0 = 1 :=
  rewrite Nat.addZero n then
  let same := h
  same

theorem twoSteps ∀ (m n: Nat) (h: m = n): m + 0 = n + 0 :=
  rewrite Nat.addZero m, Nat.addZero n then
  let same := h
  let again := same
  again
