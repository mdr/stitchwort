-- A pattern `let` that takes a proof of `And` apart outside a proof binds
-- its names to `And.left` and `And.right`, so a definition using it
-- unfolds as written even where the proof doesn't compute to `Both`.

import Std (And, Bool, Decidable, Eq, Nat, Void)

def half: Nat → Nat
  | Zero => 0
  | Succ Zero => 0
  | Succ (Succ n) => Succ (half n)

theorem halfBounds: (n: Nat) → And (half n + half n ≤ n) (n ≤ half n + half n + 1)
  | Zero => Both rfl rfl
  | Succ Zero => Both rfl rfl
  | Succ (Succ n) =>
    let (Both below above) := halfBounds n
    Both (omega [below]) (omega [above])

def firstBlocked (blocked: Nat → Bool) (low: Nat) (high: Nat): Nat
    decreasing high - low :=
  if apart: Succ low < high then
    let middle := low + half (high - low)
    let (Both below above) := halfBounds (high - low)
    if blocked middle then firstBlocked blocked low middle [decreasing := omega [below, above, apart]]
    else firstBlocked blocked middle high [decreasing := omega [below, above, apart]]
  else high

theorem firstBlockedSplit (blocked: Nat → Bool) (low: Nat) (high: Nat) (apart: Nat.leq (Succ (Succ low)) high = True):
    firstBlocked blocked low high
      = (if blocked (low + half (high - low)) then firstBlocked blocked low (low + half (high - low))
        else firstBlocked blocked (low + half (high - low)) high) :=
  rewrite firstBlocked.unfold blocked low high in
    Decidable.elimEq _ _ _ _ (isApart => rfl) (notApart => Void.exfalso (notApart apart))

-- `_` skips a field, and a lambda's parameter can be taken apart too.
def lowerHalf (n: Nat) (bounds: And (half n + half n ≤ n) (n ≤ half n + half n + 1)): Nat :=
  let (Both _ above) := bounds
  half n

def withBounds: (n: Nat) → And (half n + half n ≤ n) (n ≤ half n + half n + 1) → Nat :=
  n => (Both below _) => half n

theorem lowerHalfIsHalf (n: Nat) (bounds: And (half n + half n ≤ n) (n ≤ half n + half n + 1)): lowerHalf n bounds = half n := rfl

theorem withBoundsIsHalf (n: Nat) (bounds: And (half n + half n ≤ n) (n ≤ half n + half n + 1)): withBounds n bounds = half n := rfl
