-- expect-error: E-NO-INDUCT
-- A recursive `decreasing` definition whose body has no `if` or `match` at
-- the top (the `match` is under `Succ`) gets no equations, and so no
-- `f.induct`. The error says why, not that the function doesn't call itself.
import Std (Nat)

def halfUp (n: Nat): Nat
    decreasing n
:=
  Succ (match n with
    | Zero => Zero
    | Succ m => halfUp m)

theorem halfUpGe (n: Nat): halfUp n ≥ n :=
  match induct (halfUp n) with
    | eq n => arithmetic
