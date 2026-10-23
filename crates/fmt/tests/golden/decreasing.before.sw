-- D1038: `decreasing` is a header continuation line, at +4. R21: the bare
-- `:=` after it stays in column 0.
def settle (grid: Marked w h): Marked w h
      decreasing Marked.rolls grid
:=
      let next := sweep grid
      if fewer: Marked.rolls next < Marked.rolls grid then settle next else next

def sum (xs: List Nat) (acc: Nat): Nat
  decreasing xs.length :=
  match xs with
    | Nil => acc
    | Cons y ys => sum ys (acc + y)
