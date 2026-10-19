-- expect-error: E-LET-REFUTABLE
-- `IO.readLine()` may return `Nothing`, so `Just l` can't be the whole pattern.
def f(): {IO} Text :=
  let Just l := IO.readLine()
  l
