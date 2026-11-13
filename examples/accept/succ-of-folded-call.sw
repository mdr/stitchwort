-- A `decreasing` definition's call stays folded, and under `Succ` it is
-- still unfolded when compared with a number: `Succ (innerN 0)` is `2`,
-- directly or through a definition that returns the folded call (SW-2157).

def innerN (x: Nat): Nat
    decreasing x
:= match x with
  | Zero => 1
  | Succ m => innerN m [decreasing := omega]

def outerN (x: Nat): Nat
    decreasing x
:= match x with
  | Zero => innerN x
  | Succ m => outerN m [decreasing := omega]

def through (x: Nat): Nat := outerN x

theorem succInner: Succ (innerN 0) = 2 := rfl

theorem succOuter: Succ (outerN 3) = 2 := rfl

theorem succThrough: Succ (Succ (through 0)) = 3 := rfl
