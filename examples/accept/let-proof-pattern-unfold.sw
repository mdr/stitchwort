-- A pattern `let` that takes a proof of `And` apart outside a proof binds
-- its names to `And.left` and `And.right`, so a definition using it
-- unfolds as written even where the proof doesn't compute to `Both`.

import Std (And, Bool, Decidable, Eq, Nat, Void)

def half: Nat → Nat
  | Zero => 0
  | Succ Zero => 0
  | Succ (Succ n) => Succ (half n)

theorem halfBounds ∀ (n: Nat): (half n + half n ≤ n) ∧ (n ≤ half n + half n + 1) := match n with
  | Zero => Both byComputing byComputing
  | Succ Zero => Both byComputing byComputing
  | Succ (Succ n) =>
    let (Both below above) := halfBounds n
    Both (arithmetic [below]) (arithmetic [above])

def firstBlocked (blocked: Nat → Bool) (low high: Nat): Nat
    decreasing high - low
:=
  if apart: Succ low < high then
    let middle := low + half (high - low)
    let (Both below above) := halfBounds (high - low)
    if blocked middle then firstBlocked blocked low middle [decreasing := arithmetic [below, above, apart]]
    else firstBlocked blocked middle high [decreasing := arithmetic [below, above, apart]]
  else high

theorem firstBlockedSplit ∀ (blocked: Nat → Bool) (low high: Nat)
    (apart: Nat.leq (Succ (Succ low)) high = True):
    firstBlocked blocked low high
      = (if blocked (low + half (high - low)) then firstBlocked blocked low (low + half (high - low))
         else firstBlocked blocked (low + half (high - low)) high) :=
  rewrite firstBlocked.unfold blocked low high then
    Decidable.elimEq _ _ _ _ (isApart => byComputing) (notApart => (notApart apart).impossible)

-- `_` skips a field, and a lambda's parameter can be taken apart too.
def lowerHalf (n: Nat) (bounds: (half n + half n ≤ n) ∧ (n ≤ half n + half n + 1)): Nat :=
  let (Both _ above) := bounds
  half n

def withBounds: (n: Nat) → (half n + half n ≤ n) ∧ (n ≤ half n + half n + 1) → Nat := n => (Both below _) => half n

theorem lowerHalfIsHalf ∀ (n: Nat)
    (bounds: (half n + half n ≤ n) ∧ (n ≤ half n + half n + 1)):
    lowerHalf n bounds = half n :=
  byComputing

theorem withBoundsIsHalf ∀ (n: Nat)
    (bounds: (half n + half n ≤ n) ∧ (n ≤ half n + half n + 1)):
    withBounds n bounds = half n :=
  byComputing
