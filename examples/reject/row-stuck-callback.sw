-- expect-error: E-TYPE-MISMATCH
-- A callback whose result type is stuck on a variable (`Answer flag`) is
-- neither `Nat` nor a computation over some row, whatever `flag` is, so no
-- row fits `twice`'s `f: () -> {e} Nat`.
def Answer: Bool → Type
  | True => Text
  | False => Nat

def twice (f: () → {e} Nat): {e} Nat :=
  let a := f ()
  let b := f ()
  a + b

def stuck [flag: Bool] (h: () → Answer flag): Nat :=
  let g := (u: ()) => twice h
  0
