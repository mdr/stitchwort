-- expect-error: E-PARSE
-- An `else` left of the line its `if` is on can't continue it: it would belong
-- to the enclosing `if`, which already has its `then` branch complete.
def g (a : Bool) : Nat :=
  if a then
    if a then 1
  else 2
