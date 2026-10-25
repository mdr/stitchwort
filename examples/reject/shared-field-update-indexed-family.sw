-- expect-error: E-RECORD-UPDATE
-- A value of an indexed family cannot be updated by field.

type Fam: Nat → Type =
  | F0 (k: Nat): Fam 0
  | F1 (k: Nat): Fam 1

def f (a: Fam 0): Fam 0 := { a | k = 1 }
