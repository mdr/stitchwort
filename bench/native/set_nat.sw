-- The N1 `Set` benchmark (native-compilation.md, Appendix A): build a set of
-- Nats by inserting the keys (i * 7919) % 1009 and print its size. 1,000 keys
-- here; the speed measurements use 1,000,000 keys.
import Std (IO, List, Set)

def keys (n: Nat): List Nat := List.map (List.range n) (i => (i * 7919) % 1009)

def main(): {IO} () :=
  IO.print "${Set.size (Set.fromList (keys 1000))}"
