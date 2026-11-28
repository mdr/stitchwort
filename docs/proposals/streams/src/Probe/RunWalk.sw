namespace Probe.RunWalk

import Probe.Walk (Stream, Cells)

-- Walking by repeated `tail`, the way a hand-written loop over head and tail would.
def sumByTail (s: Stream Nat) (n acc: Nat): Nat := match n with
  | Zero => acc
  | Succ k => sumByTail s.tail k (acc + s.head)

def main(): {IO} () :=
  IO.print "${sumByTail (Stream.iterate (+ 1) 0) 2000 (((Stream.iterate (+ 1) 0).walk 2000).sum 0)}"
