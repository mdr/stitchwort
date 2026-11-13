-- A `match` whose scrutinee is found only in a hypothesis the goal mentions
-- copies that hypothesis, so each arm's goal is about the refined copy
-- (`h : True = True`), not the original: the goal is not kept as written
-- (SW-2554 review, F6).
import Std (Nat)

theorem copied ∀ (n: Nat) (h: Nat.leq n 1 = True): h = h := match Nat.leq n 1 with
  | True => ?
  | False => ?
