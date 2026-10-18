-- expect-error: E-LET-REFUTABLE
-- `readLine ()` may return `Nothing`, so `Just l` can't be the whole pattern.
f : () -> {IO} Text
f u =
  let Just l = readLine ()
  l
