-- expect-error: E-LET-REFUTABLE
-- `readLine ()` may return `Nothing`, so `Just l` can't be the whole pattern.
def f (): {IO} Text :=
  let Just l := readLine ()
  l
