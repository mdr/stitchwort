-- expect-error: E-TYPE-MISMATCH
-- A call leaving out a parameter, whose argument waits: `r.xs` waits for
-- `r`'s type, which only `made p` fixes, and fails once it is known, after
-- the call has been checked. It still gets the notes on the parameter left
-- out, worked out then, as when `r` is annotated (`annotated`): the check
-- carries the call's error frame (docs/proposals/postponement.md, step 4.1,
-- D2091).

import Std (Vec)

def use (n: Nat) (xs: Vec Nat n): Nat := n

type P = { xs: Vec Nat 3 }

def later (p: P): (n: Nat) → Nat :=
  let made := r => use (xs := r.xs)
  made p

def annotated (p: P): (n: Nat) → Nat :=
  let made := (r: P) => use (xs := r.xs)
  made p
