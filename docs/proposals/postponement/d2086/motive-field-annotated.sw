-- D2086: control for motive-field-later.sw, with `r` annotated.
import Std (List)

type P = { x: Nat }

def two (m: Nat) (p: m = 2): Bool → Nat
  | True => m
  | False => 0

def apply (f: a → Nat) (v: a): Nat := f v

def annotated (b: Bool) (q: two 2 rfl b = 2) (p: P): Nat :=
  apply
    ((r: P) =>
      match List.length [r.x, r.x] with
        | Zero => 0
        | Succ k => k)
    p
