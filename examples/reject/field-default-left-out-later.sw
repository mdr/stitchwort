-- expect-error: E-TYPE-MISMATCH
-- A field given after one left out, whose check waits: `r.cells` waits for
-- `r`'s type, which only `made p` fixes, and fails once it is known, after
-- the value has been built. It still gets the note on the field left out,
-- as when `r` is annotated (`annotated`): the check carries the field's
-- error frame (docs/proposals/postponement.md, step 4.1, D2091).

import Std (Vec)

type Sized = {
  size: Nat := 0,
  cells: Vec Bool size
}

type P = { cells: Vec Bool 3 }

def later (p: P): Sized :=
  let made := r => ({ cells = r.cells }: Sized)
  made p

def annotated (p: P): Sized :=
  let made := (r: P) => ({ cells = r.cells }: Sized)
  made p
