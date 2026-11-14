-- `omega` reads arithmetic after it has computed, so it reads what a number
-- added inside turns into (SW-997). `(n + 1).toInt - 1` computes to
-- `Int.subNatNatFrom (n + 1) 1 (0 - n)`: `1 - (n + 1)` has taken a step to
-- `0 - n`. `(n + 1) / 2` computes to a step of the division,
-- `Nat.divStep (1 <= n) n (n + 1) 2`, and `(n + 3) / 2` to one more than a
-- step whose fuel is larger than its numerator. Each is read as the
-- subtraction or division it comes from.

import Std (And, Bool, Eq, Int, Nat, Not, Or, Void)

-- `Int` subtraction after the numbers have met (AoC 2021 day 17).
theorem predNonneg ∀ (i: Nat): 0 ≤ i.toInt + 1 - 1 := omega

theorem predBack ∀ (n: Nat): (n + 1).toInt - 1 = n.toInt := omega

theorem predBelow ∀ (n: Nat): (n + 1).toInt - 1 ≤ (n + 1).toInt := omega

theorem bothSucc ∀ (n m: Nat): (n + 2).toInt - (m + 1).toInt = n.toInt - m.toInt + 1 := omega

theorem oneMinus ∀ (n: Nat): 1 - (n + 1).toInt = -n.toInt := omega

theorem negPlus ∀ (n: Nat): -((n + 1).toInt) + 1 = -n.toInt := omega

theorem minusMore ∀ (n: Nat): (n + 2).toInt - 5 = n.toInt - 3 := omega

theorem constantFirst ∀ (n: Nat): -3 + (n + 1).toInt = n.toInt - 2 := omega

theorem doubled ∀ (n: Nat): (n + 1).toInt * 2 - 2 = 2 * n.toInt := omega

-- `Nat` division of a numerator with a number added.
theorem halfBelow ∀ (n: Nat): (n + 1) / 2 ≤ n + 1 := omega

theorem halfAfterStep ∀ (n: Nat): (n + 3) / 2 ≤ n + 2 := omega

theorem twiceHalf ∀ (n: Nat): 2 * ((n + 4) / 2) ≤ n + 4 := omega

theorem halfStepped ∀ (n: Nat): (n + 3) / 2 = (n + 1) / 2 + 1 := omega

theorem parity ∀ (n: Nat): (n + 1) % 2 < 2 := omega

theorem intHalf ∀ (n: Nat): ((n + 3).toInt - 1) / 2 ≤ n.toInt + 2 := omega

-- Disjunctions from a goal's other side wait for the case that settles
-- them: here `h`'s three cases, each with the sign's three, and the facts
-- `… = False` that proving the goal `(a || b || c) = True` side by side
-- leaves (AoC 2021 day 17's `pastStays`, without naming the parts).
type Probe = { x: Int, y: Int, dx: Int, dy: Int }

def overshot (right: Int) (probe: Probe): Bool := right < probe.x ∧ 0 ≤ probe.dx

def short (left: Int) (probe: Probe): Bool := probe.x < left ∧ probe.dx ≤ 0

def fallen (bottom: Int) (probe: Probe): Bool := probe.y < bottom ∧ probe.dy < 0

def past (left right bottom: Int) (probe: Probe): Bool := overshot right probe ∨ short left probe ∨ fallen bottom probe

def step (probe: Probe): Probe :=
  { x = probe.x + probe.dx, y = probe.y + probe.dy, dx = probe.dx - Int.sign probe.dx, dy = probe.dy - 1 }

theorem signCases ∀ (dx: Int): (Int.sign dx = 1 ∧ 0 < dx) ∨ (Int.sign dx = 0 ∧ dx = 0) ∨ (Int.sign dx = -1 ∧ dx < 0) :=
  match dx with
    | OfNat 0 => Inr (Inl (Both rfl rfl))
    | OfNat (Succ k) => Inl (Both rfl (omega))
    | NegSucc k => Inr (Inr (Both rfl (omega)))

theorem pastStays ∀ (left right bottom: Int) (probe: Probe)
    (h: past left right bottom probe = True):
    past left right bottom (step probe) = True :=
  omega [signCases probe.dx]
