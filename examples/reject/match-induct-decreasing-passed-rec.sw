-- expect-error: E-NO-INDUCT
-- A `decreasing` definition that passes its recursive call to another
-- function (`twice`, not one of `hf`'s own helpers) gets no `hf.induct`:
-- the call is under the function's binder, and `twice`'s body isn't read as
-- if it were a `match` of `hf`'s.
import Std (Bool, Eq, Nat)

def twice (k: Nat) (g: (y: Nat) → y < k → Nat): Nat := match k with
  | Zero => 0
  | Succ j => g j (Nat.leRefl k)

theorem twiceCong ∀ (k: Nat) (f1 f2: (y: Nat) → y < k → Nat)
    (e: ∀ (y: Nat) (p: y < k) => f1 y p = f2 y p):
    twice k f1 = twice k f2 :=
  match k with
    | Zero => byComputing
    | Succ j => e j (Nat.leRefl (Succ j))

def hf (n: Nat): Nat
    decreasing n
:=
  if n == 100 then 0 else Succ (twice n (y p => hf y [decreasing := p]))

theorem hfAtLeastZero ∀ (n: Nat): hf n ≥ 0 := match induct (hf n) with
  | eqIfTrue n h => arithmetic
  | eqIfFalse n h => arithmetic
