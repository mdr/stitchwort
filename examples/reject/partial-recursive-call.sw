-- expect-error: E-TERMINATION
-- A recursive call given only some of its arguments stands for a function
-- of the rest, which the termination checker knows nothing about. Here the
-- argument that gets smaller is the second, and it isn't given: the call
-- passed along is `x => sumFrom (acc + 1) x`, and nothing says `x` is
-- smaller than `Succ n`. Neighbour: accept/partial-recursive-call.sw, where
-- the argument that gets smaller is given.
def applyTo (f: Nat → Nat) (x: Nat): Nat := f x

def sumFrom: Nat → Nat → Nat
  | acc, Zero   => acc
  | acc, Succ n => applyTo (sumFrom (acc + 1)) n
