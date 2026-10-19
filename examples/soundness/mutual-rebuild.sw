-- expect-error: E-TERMINATION
-- Rebuilding the matched value isn't smaller than it, across a group too:
-- `a 1` loops (§6.8, example 13).
-- Neighbour: `isEven`/`isOdd` in accept/mutual.sw, which pass the smaller
-- `n`.
def a: Nat -> Nat
  | Zero   => Zero
  | Succ n => b (Succ n)

def b: Nat -> Nat
  | Zero   => Zero
  | Succ n => a (Succ n)
