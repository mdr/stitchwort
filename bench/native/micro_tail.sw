-- N1 tail-call benchmark: a tail-recursive loop (native-compilation.md
-- section 1.3). Small size here; the measurements use 20,000,000 iterations.
import Std (IO)

def spin: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ n, acc => spin n (acc + n)

def main(): {IO} () :=
  IO.print "${spin 1000 0}"
