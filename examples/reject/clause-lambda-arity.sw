-- expect-error: E-PARSE
-- Every arm of a clause lambda has one pattern for each parameter; the
-- first arm says how many.
import Std (Nat)

def f: Nat → Nat → Nat := match
  | 0, y => y
  | x => x
