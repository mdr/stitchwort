-- expect-error: E-PARSE
-- A local function is a `def`: a `let` binds a value, so it takes no
-- parameters. The note points at the `def` form (docs/syntax.md, "Local
-- definitions").

def addTo (n: Nat): Nat :=
  let add (y: Nat): Nat := y + n
  add 1
