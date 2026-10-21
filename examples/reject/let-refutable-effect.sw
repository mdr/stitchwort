-- expect-error: E-LET-REFUTABLE
-- `IO.readLine()` may return `None`, so `Some l` can't be the whole pattern.
def f(): {IO} Text :=
  let Some l := IO.readLine()
  l
