-- expect-error: E-TERMINATION
-- A recursive call must be given all its arguments, even when the ones it's
-- given would be enough to see that it terminates: the termination checker
-- relates each call to everything the function receives. Write
-- `\x -> sumWith n x` (as in accept/size-change.sw).
def applyTo (f : Nat -> Nat) (x : Nat) : Nat := f x

def sumWith : Nat -> Nat -> Nat
  | Zero,   acc => acc
  | Succ n, acc => applyTo (sumWith n) (acc + Succ n)
