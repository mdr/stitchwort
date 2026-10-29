-- `cases` whose goal has an unknown solved after the goal was computed:
-- `ok`'s `a` is solved as `Nat` by `MkBox 3`, after the type of `h` was
-- written with it. The goal is still `Box Nat = Box Nat`, closed by
-- computation, and `Box Nat = Box Bool` is still the hypothesis `h0`
-- (SW-862: the kernel's conversion compares unknowns by their numbers).
type Box (a: Type) =
  | MkBox (x: a)

def ok [a: Type] (b: Box a) (h: Box a = Box Nat): Nat := 0

def byComputation: Nat := ok (MkBox 3) cases

def okBool [a: Type] (b: Box a) (h: Box a = Box Bool): Nat := 0

def byHypothesis (h0: Box Nat = Box Bool): Nat := okBool (MkBox 3) cases
