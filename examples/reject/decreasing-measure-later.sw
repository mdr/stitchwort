-- expect-error: E-TYPE-MISMATCH
-- A `decreasing` measure that waits: `r.x` waits for `r`'s type, which only
-- `size p` fixes, and fails when the measure is finished, after its check
-- has returned. It still gets the note on what a measure is, as when `r` is
-- annotated (`annotated`): the check carries the measure's error frame
-- (docs/proposals/postponement.md, step 4.1, D2091).

import Std (Nat, Text)

type P = { x: Text }

def later (p: P) (n: Nat): Nat
    decreasing (let size := r => r.x; size p)
:=
  match n with
    | Zero => 0
    | Succ k => later p k

def annotated (p: P) (n: Nat): Nat
    decreasing (let size := (r: P) => r.x; size p)
:=
  match n with
    | Zero => 0
    | Succ k => annotated p k
