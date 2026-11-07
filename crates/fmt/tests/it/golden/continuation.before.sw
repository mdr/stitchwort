-- D1040: a continuation line goes at +2 from the line it continues, however
-- far the author indented it. The nesting of the lines is kept.
def f (x: Nat): Nat :=
      g x
         (h x)
           x

def staircase (a: Nat) (b: Nat): Nat :=
  Eq.trans (Eq.cong f a)
           (Eq.trans (Eq.cong g b)
                     (Eq.refl b))

-- Lines of one block share a column and continue alike.
def block (x: Nat): Nat :=
    let y := foo x
                 x
    let z := bar y
    z
