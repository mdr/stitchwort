-- Chapter 7: `List.map` with a partial callback is partial too.
import Std (IO, List, Nat)

def collatzSteps: Nat -> {Partial} Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def stepsOfAll (numbers: List Nat): {Partial} (List Nat) := List.map numbers collatzSteps

def main(): {IO, Partial} () := IO.print "steps: ${stepsOfAll [3, 7, 27]}"
