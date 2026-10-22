-- Two library loops that don't end by themselves, so each takes what makes it
-- end (`decreasing`, docs/proposals/well-founded-recursion.md): a measure of
-- the state and a proof that the measure shrinks at every step.
--
--   `List.unfold seed step measure shrinks` builds a list from a seed;
--   `Nat.iterateUntilStable x step measure shrinks` applies `step` until it
--   changes nothing.
--
--   $ stitchwort run examples/accept/unfold-until-stable.sw
--   countdown sum: 15
--   water left: 0
--   steps: 7

import Std (Eq, IO, List, Nat, Option, Pair, Text, Void)

-- A countdown: `None` at zero, else the number, going on from one less.
def countdown: Nat -> Option (Pair Nat Nat)
  | Zero   => None
  | Succ k => Some (MkPair (Succ k) k)

-- `shrinks` for it: whatever step `countdown` takes from `x`, the new seed
-- is smaller. A step is `Some (MkPair v y)`, so `y` is the `k` it made.
theorem countdownShrinks (x: Nat) (y: Nat) (v: Nat) (h: countdown x = Some (MkPair v y)): y < x :=
  match x with
    | Zero => Void.exfalso (Option.noneNotSome (MkPair v y) h)
    | Succ k =>
      let e := Pair.mkInjectiveSnd (Succ k) k v y (Option.someInjective (MkPair (Succ k) k) (MkPair v y) h)
      Nat.ltCongLeft k y (Succ k) e (Nat.leRefl (Succ k))

def countdownFrom (n: Nat): List Nat := List.unfold n countdown (k => k) countdownShrinks

test "unfold" := countdownFrom 5 == [5, 4, 3, 2, 1]
test "unfold, nothing to do" := countdownFrom 0 == []

-- A tank that loses one unit at a time, until it is empty.
def drain (water: Nat): Nat := water - 1

theorem drainShrinks: (water: Nat) -> Not (drain water = water) -> drain water < water
  | Zero,      empty => Void.exfalso (empty rfl)
  | Succ left, empty => Nat.leRefl (Succ left)

def settle (water: Nat): Nat := Nat.iterateUntilStable water drain (w => w) drainShrinks

test "until stable" := settle 7 == 0 && settle 0 == 0

-- What it returns is a fixed point, for every starting value.
theorem settleIsStable (water: Nat): drain (settle water) = settle water :=
  Nat.iterateUntilStableFixed water drain (w => w) drainShrinks

-- A value that is already stable is the answer.
theorem settleStays: settle 0 = 0 := Nat.iterateUntilStableStable 0 drain (w => w) drainShrinks rfl

def main(): {IO} () :=
  IO.print ("countdown sum: " ++ Nat.toText (List.sum (countdownFrom 5)))
  IO.print ("water left: " ++ Nat.toText (settle 7))
  IO.print ("steps: " ++ Nat.toText (List.length (countdownFrom 7)))
