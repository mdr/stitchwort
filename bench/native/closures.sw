-- The N3 closure benchmark (native-compilation.md, "N3 as built"): map a list
-- through lambdas that capture values, filter it, and fold it with a lambda
-- and with a partial application. 1,000 elements here; the speed
-- measurements use 1,000,000.
import Std (IO, List)

def add (a: Nat) (b: Nat): Nat := a + b

def run (n: Nat): Nat :=
  let scale := n % 7 + 4
  let offset := n % 11
  let xs := List.range n
  let ys := List.map xs (x => (x * scale + offset) % 1000003)
  let zs := List.filter ys (y => y % 3 != offset % 3)
  let total := List.foldLeft zs 0 (acc z => (acc + z * scale) % 1000000007)
  List.foldLeft (List.map zs (add offset)) total add % 1000000007

def main(): {IO} () :=
  IO.print "${run 1000}"
