-- expect-error: E-TERMINATION
-- A member of a group passed bare to a helper, which hides what it's called
-- on (§6.8, example 12): refused, because a member must be given all its
-- arguments wherever it's used in the group.
-- Neighbour: `walk`/`stepBy` in accept/mutual.sw, which passes
-- `x => stepBy k x` with `k` smaller.
def applyTo (f: List Nat -> Nat) (xs: List Nat): Nat := f xs

def walk (ts: List Nat): Nat := applyTo walkList ts

def walkList: List Nat -> Nat
  | Nil       => 0
  | Cons _ ts => walk ts
