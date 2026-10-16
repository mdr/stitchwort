-- expect-error: E-PARTIAL
-- A row variable never stands for `Partial`: `simulate`'s program must be
-- total. A partial `main` is run by `stitchwort run` instead.
cat : () -> {IO, Partial} ()
cat u =
  print "again"
  cat ()

printed : List Text
printed = fst (simulate [] cat)
