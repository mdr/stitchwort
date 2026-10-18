-- expect-error: E-TERMINATION
-- The same, written with a lambda so every call has its arguments: the call
-- `walkList x` is on the lambda's `x`, which isn't known to be smaller than
-- anything, so going round `walk → walkList → walk` nothing gets smaller.
-- (`walk Nil` would loop.)
-- Neighbour: `walk`/`stepBy` in accept/mutual.sw.
def applyTo (f : List Nat -> Nat) (xs : List Nat) : Nat := f xs

def walk (ts : List Nat) : Nat := applyTo (\x => walkList x) ts

def walkList : List Nat -> Nat
  | Nil       => walk Nil
  | Cons _ ts => walk ts
