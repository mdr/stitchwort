-- expect-error: E-PARSE
-- A line can't start with a method section as an argument: `.map f` here could
-- be read as one more argument of `foo`. Write `xs |> .map f` or `(.map f)`.

def foo (xs: List Nat): List Nat := xs

def g (xs: List Nat): List Nat :=
  foo xs
    .map (\x => x)
