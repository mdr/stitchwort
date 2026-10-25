-- N1 call benchmark: non-tail calls, 20 deep, repeated (native-compilation.md
-- section 1.3). Small sizes here; the measurements use 1,000,000 outer
-- iterations.
import Std (IO)

def down: Nat → Nat
  | Zero => 0
  | Succ n => 1 + down n

def outer: Nat → Nat → Nat
  | Zero, acc => acc
  | Succ k, acc => outer k (acc + down 20)

def main(): {IO} () :=
  IO.print "${outer 1000 0}"
