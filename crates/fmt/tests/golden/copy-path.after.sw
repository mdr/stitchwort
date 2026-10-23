-- Lines no rule covers yet keep their distance from the line they continue,
-- and move with it.
def f (x: Nat): Nat :=
  g x
     (h x)
       x

-- If the rules would reorder or merge the columns of one line's children,
-- they all keep their distances: here the body would move to +2, left of
-- the leading comma.
def xs: List Nat :=
    [1
  , 2]
