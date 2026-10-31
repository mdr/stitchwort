-- expect-error: E-CALC-STEP
-- A `calc` step whose `rfl` waits: `r.x` waits for `r`'s type, which only
-- `proof p` fixes, so the step's comparison waits for it too and fails after
-- the `calc` has returned. It is still the step's error, as when `r` is
-- annotated (`annotated`): the check carries the step's error frame
-- (docs/proposals/postponement.md, step 4.1, D2091).

import Std (Bool, Nat)

type P = { x: Nat }

def later (p: P): Bool :=
  let proof := r => (calc r.x
    _ = 5 := rfl)
  let _ := proof p
  True

def annotated (p: P): Bool :=
  let proof := (r: P) => (calc r.x
    _ = 5 := rfl)
  let _ := proof p
  True
