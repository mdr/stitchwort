-- D2086: a `match` whose scrutinee holds an ordinary unknown (a lambda
-- parameter's type, fixed by a later argument), generalising a hypothesis.
import Std (List)

type P = { x: Nat }

def one (m: Nat) (p: m = 1): Bool → Nat
  | True => m
  | False => 0

def apply (f: a → Nat) (v: a): Nat := f v

def annotated (b: Bool) (q: one 1 rfl b = 1) (p: P): Nat :=
  apply
    ((r: P) =>
      match List.length [r] with
        | Zero => 0
        | Succ k => k)
    p
