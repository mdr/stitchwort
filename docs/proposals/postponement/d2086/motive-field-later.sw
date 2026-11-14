-- D2086: a `match` whose scrutinee holds a `.field` waiting for its
-- receiver's type (stage 2's K2), generalising a hypothesis.
import Std (List)

type P = { x: Nat }

def two (m: Nat) (p: m = 2): Bool → Nat
  | True => m
  | False => 0

def apply (f: a → Nat) (v: a): Nat := f v

-- `r`'s type is fixed by the later argument `p`.
def later (b: Bool) (q: two 2 rfl b = 2) (p: P): Nat :=
  apply
    (r =>
      match List.length [r.x, r.x] with
        | Zero => 0
        | Succ k => k)
    p
