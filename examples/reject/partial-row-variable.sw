-- expect-error: E-PARTIAL
-- A row variable never stands for `Partial`: `IO.simulate`'s program must be
-- total. A partial `main` is run by `stitchwort run` instead.
def cat(): {IO, Partial} () :=
  IO.print "again"
  cat()

def printed: List Text := Pair.fst (IO.simulate [] cat)
