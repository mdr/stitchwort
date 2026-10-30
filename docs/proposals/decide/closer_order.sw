-- Review 1's ordering question: should the decision closer come before or
-- after `omega`? Three facts measured here (decide.md §6.1.2).
import Std (Bool, List, Nat, Void)

def byDecision [p: Prop] [auto h: p]: p := h

type Key =
  | K0
  | K1
  | K2

def keys: List Key := [K0, K1, K2]

-- 1. A closed goal that decides false, in a case whose hypotheses
-- contradict each other: `omega` proves it today. A decision closer that
-- failed the case on `No` would turn this proof into an error, so `No` must
-- fall through to the other steps, wherever the closer sits.
theorem falseGoalImpossibleCase (n: Nat) (h: n + 1 < n): 2 ∈ [1, 3] := cases

-- 2. Where both apply, a closed proposition: both take about 0.1 ms.
theorem overlapOmega: Or (5 < 4) (Not (2 = 3)) := omega

theorem overlapDecision: Or (5 < 4) (Not (2 = 3)) := byDecision

-- 3. Where only the decision closer applies, `omega` fails first, at about
-- 0.1 ms and 1,211 steps (`theorem enterByOmega: K1 ∈ keys := omega` is
-- `E-OMEGA`: "`omega` can't prove `Void`").
theorem enterByDecision: K1 ∈ keys := byDecision

-- `Decidable.or` decides left to right: a left side that decides `Yes` is
-- enough, with the right side stuck on `flag`. (A stuck left side is stuck
-- even when the right side is true: `Or (key ∈ keys) (True = True)` is
-- `E-AUTO-STUCK`.)
theorem leftYes (flag: Bool): Or (K1 ∈ keys) (flag = True) := byDecision
