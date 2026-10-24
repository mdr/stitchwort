-- Chapter 7: a function that may not finish says so with `Partial`.
import Std (IO, Nat)

def collatzSteps: Nat -> {Partial} Nat
  | 0 => 0
  | 1 => 0
  | n => 1 + collatzSteps (if n % 2 == 0 then n / 2 else 3 * n + 1)

def main(): {IO, Partial} () := IO.print "27 takes ${collatzSteps 27} steps"
