-- expect-error: E-TYPE-MISMATCH
-- An argument of a local definition that waits: `r.x` waits for `r`'s type,
-- which only `p` fixes, and fails once it is known, after the argument's
-- check has returned. It still gets the note with the local definition's
-- signature, as when `r` is annotated (`annotated`): the check carries the
-- argument's error frame (docs/proposals/postponement.md, step 4.1, D2091).

import Std (Nat)

type P = { x: Nat }

def apply (f: a → b) (v: a): b := f v

def reach: List Nat → Nat → Nat → Bool
  | ls, c, Zero => False
  | Nil, c, Succ k => False
  | Cons line rest, c, Succ k =>
    def left: Nat → Bool
      | Zero => False
      | Succ b => reach rest b k
    left c

def later (rest: List Nat) (k: Nat) (p: P): Bool := apply (r => reach.left r.x k Zero) p

def annotated (rest: List Nat) (k: Nat) (p: P): Bool := apply ((r: P) => reach.left r.x k Zero) p
