-- expect-error: E-AUTO-FALSE
-- An arm with a condition above a catch-all gives it no fact: the
-- catch-all is reached with `n = 5` when the condition fails, so `auto`
-- can't prove `m ≠ 5` there (docs/proposals/catch-all-facts.md).
import Std (Bool, Nat)

def apartFromFive (n: Nat) [auto ok: n ≠ 5]: Nat := n

def afterGuard (n: Nat) (b: Bool): Nat := match n with
  | 5 if b => 0
  | m => apartFromFive m
