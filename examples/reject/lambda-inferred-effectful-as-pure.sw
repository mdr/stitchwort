-- expect-error: E-TYPE-MISMATCH
-- A lambda with no type written whose body performs `Ask` has type
-- `Nat → {Ask} Nat`, so it can't be passed where a pure function is
-- expected.
ability Ask where
  ask: () → {Ask} Nat

def applyPure (f: Nat → Nat) (n: Nat): Nat := f n

def addAsked (n: Nat): {Ask} Nat :=
  let add := x => x + ask()
  applyPure add n
