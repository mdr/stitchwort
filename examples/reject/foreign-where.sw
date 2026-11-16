-- expect-error: E-WHERE
-- Haskell's `where` clause: a helper is a local `def` in the body's block.
def f (n: Nat): Nat := g n
  where
    g (x: Nat): Nat := x + 1
