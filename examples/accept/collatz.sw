-- The Collatz sequence: nobody knows whether it reaches 1 from every
-- number, so counting its steps is `Partial`.
--
--   $ stitchwort run examples/accept/collatz.sw
--   27 reaches 1 in 111 steps
--
-- Each recursive call is one tick of the runtime (docs/proposals/partial.md
-- §7.4.3): `collatzSteps 27` takes 111 ticks, one per step, and
-- `collatzSteps 1` none. crates/driver/tests/partial.rs checks those counts
-- against the runtime's model.

import Std (Nat)

-- The next number in the sequence: total, so it can be tested and proved
-- about.
def next (n: Nat): Nat := if n % 2 == 0 then n / 2 else 3 * n + 1

test "after 27" := next 27 == 82

test "after 82" := next 82 == 41

def collatzSteps: Nat → {Partial} Nat
  | 1 => 0
  | n => 1 + collatzSteps (next n)

def main(): {IO, Partial} () := IO.print ("27 reaches 1 in " ++ Nat.toText (collatzSteps 27) ++ " steps")
