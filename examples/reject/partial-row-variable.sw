-- expect-error: E-PARTIAL
-- A row variable never stands for `Partial`: `IO.simulate`'s program must be
-- total. A partial `main` is run by `stitchwort run` instead.
cat : () -> {IO, Partial} ()
cat u =
  print "again"
  cat ()

printed : List Text
printed = Pair.fst (IO.simulate [] cat)
